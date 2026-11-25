import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: the timestamp response and its status

From 0xA60 to 0xB06: the timestamp must be one `SEQUENCE` with nothing after it, and its first element a `SEQUENCE` that holds `INTEGER 0` and nothing else.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTr1a60 : List BInstr :=
  [.alu .add a2 x0 (19 : Fin 32)]
theorem svTr1a60_end : blockEnd sigstoreVerifyCode 0xA60 svTr1a60 = some 0xA62 := by
  simp only [svTr1a60]
  rw [blockEnd, sv_at_a60]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr1a66 : List BInstr :=
  [.aluImm .add a2 sp 0x280]
theorem svTr1a66_end : blockEnd sigstoreVerifyCode 0xA66 svTr1a66 = some 0xA68 := by
  simp only [svTr1a66]
  rw [blockEnd, sv_at_a66]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr1a70 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x2D0]
theorem svTr1a70_end : blockEnd sigstoreVerifyCode 0xA70 svTr1a70 = some 0xA76 := by
  simp only [svTr1a70]
  rw [blockEnd, sv_at_a70]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a74]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr1a8a : List BInstr :=
  [.aluImm .add a1 sp 0x425, .aluImm .add a0 sp 0x2E5, .aluImm .add a2 x0 0xB]
theorem svTr1a8a_end : blockEnd sigstoreVerifyCode 0xA8A svTr1a8a = some 0xA94 := by
  simp only [svTr1a8a]
  rw [blockEnd, sv_at_a8a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a8e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a92]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr114c : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x1]
theorem svTr114c_end : blockEnd sigstoreVerifyCode 0x14C svTr114c = some 0x14E := by
  simp only [svTr114c]
  rw [blockEnd, sv_at_14c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr1aac : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x2E0]
theorem svTr1aac_end : blockEnd sigstoreVerifyCode 0xAAC svTr1aac = some 0xAB2 := by
  simp only [svTr1aac]
  rw [blockEnd, sv_at_aac]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_ab0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr1ac6 : List BInstr :=
  [.aluImm .add a1 sp 0x425, .aluImm .add a0 sp 0x2F5, .aluImm .add a2 x0 0xB]
theorem svTr1ac6_end : blockEnd sigstoreVerifyCode 0xAC6 svTr1ac6 = some 0xAD0 := by
  simp only [svTr1ac6]
  rw [blockEnd, sv_at_ac6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_aca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_ace]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr1ae0 : List BInstr :=
  [.aluImm .add a0 sp 0x2F0, .aluImm .add a1 x0 0x0]
theorem svTr1ae0_end : blockEnd sigstoreVerifyCode 0xAE0 svTr1ae0 = some 0xAE4 := by
  simp only [svTr1ae0]
  rw [blockEnd, sv_at_ae0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_ae2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr1aec : List BInstr :=
  [.aluImm .and a0 a0 0x1, .alu .add (8 : Fin 32) x0 a1]
theorem svTr1aec_end : blockEnd sigstoreVerifyCode 0xAEC svTr1aec = some 0xAF0 := by
  simp only [svTr1aec]
  rw [blockEnd, sv_at_aec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_aee]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr1af4 : List BInstr :=
  [.aluImm .and a0 (8 : Fin 32) 0x1, .aluImm .add (8 : Fin 32) x0 0x18]
theorem svTr1af4_end : blockEnd sigstoreVerifyCode 0xAF4 svTr1af4 = some 0xAFA := by
  simp only [svTr1af4]
  rw [blockEnd, sv_at_af4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_af8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tr1 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 tsp tsl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xA60 (reg n0))
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
    (htsp : memLoad32 M0 (bp + 0x20) = tsp)
    (htsl : memLoad32 M0 (bp + 0x24) = tsl)
    (htsp_in : SvIn B (bp + 0x20) 4)
    (htsl_in : SvIn B (bp + 0x24) 4)
    (atsp : (bp + 0x20).toNat % 4 = 0)
    (atsl : (bp + 0x24).toNat % 4 = 0)
    (ts_in : SvIn B tsp tsl.toNat) :
    (¬ (∃ tl10, derElement 0x30 (memBytes M0 (tsp) (tsl).toNat) = .ok tl10 ∧ ((tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) = 0) ∧ ∃ tl21, derElement 0x30 (memBytes M0 ((tsp) + BitVec.ofNat 32 tl10.header) (BitVec.ofNat 32 tl10.len).toNat) = .ok tl21 ∧ derIntIsOf M0 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) (BitVec.ofNat 32 tl21.len).toNat) (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) (derElement 2 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) (BitVec.ofNat 32 tl21.len).toNat)) ((BitVec.ofNat 32 0x0).extractLsb' 0 8) = .ok true ∧ ∃ te30, derElement 2 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) (BitVec.ofNat 32 tl21.len).toNat) = .ok te30 ∧ ((BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl10, derElement 0x30 (memBytes M0 (tsp) (tsl).toNat) = .ok tl10 ∧
    ((tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) = 0) ∧
    ∃ tl21, derElement 0x30 (memBytes M0 ((tsp) + BitVec.ofNat 32 tl10.header) (BitVec.ofNat 32 tl10.len).toNat) = .ok tl21 ∧
    derIntIsOf M0 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) (BitVec.ofNat 32 tl21.len).toNat) (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) (derElement 2 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) (BitVec.ofNat 32 tl21.len).toNat)) ((BitVec.ofNat 32 0x0).extractLsb' 0 8) = .ok true ∧
    ∃ te30, derElement 2 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) (BitVec.ofNat 32 tl21.len).toNat) = .ok te30 ∧
    ((BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xB06 (reg n') ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) ∧
        SvKeepL B n0.mem n'.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xA60
  obtain ⟨n1, c1, u1⟩ := s0.block svTr1a60 E0.self svTr1a60_end
    ⟨trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0xA62 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTr1a60 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_12 : reg n1 a2 = bp := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr1a60, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  -- 0xA62: lw outside the stack
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_a62 (off' := 0xA64) (by decide)
    (by rw [g1_12]; exact atsp)
  have s2 : St n2.mem SV n2 0xA64 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_12 : reg n2 a2 = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_12]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = x27 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_10 : reg n2 a0 = tsp := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_12, sv_ld fR1 htsp_in, htsp]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  clear g1_12 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0xA64: lw outside the stack
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_a64 (off' := 0xA66) (by decide)
    (by rw [g2_12]; exact atsl)
  have s3 : St n3.mem SV n3 0xA66 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_10 : reg n3 a0 = tsp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_10]
  have g3_12 : reg n3 a2 = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_12]
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
  have g3_11 : reg n3 a1 = tsl := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_12, sv_ld fR2 htsl_in, htsl]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  clear g2_10 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_12 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0xA66
  obtain ⟨n4, c4, u4⟩ := s3.block svTr1a66 E3.self svTr1a66_end
    ⟨trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0xA68 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svTr1a66 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_10 : reg n4 a0 = tsp := by
    rw [rb4, runBlock_reg _ _ _ a0 s3.zero (by decide), g3_10]
  have g4_11 : reg n4 a1 = tsl := by
    rw [rb4, runBlock_reg _ _ _ a1 s3.zero (by decide), g3_11]
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
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = x27 := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_12 : reg n4 a2 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svTr1a66, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_10, g3_11, g3_12, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  clear g3_11 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_12 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0xA68: sw
  obtain ⟨n5, d5, s5, fr5, K5, W5, rg5⟩ := sv_sw F E4 s4 sv_at_a68 (off' := 0xA6A) (c := 0x2D0)
    (by decide) (by rw [g4_12]; sv_addr) (by decide) (by decide)
  have t5 : Steps n0 n5 := t4.trans d5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keep K5 (by decide)
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rg5 sp, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg5 (3 : Fin 32), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg5 (4 : Fin 32), g4_4]
  have g5_10 : reg n5 a0 = tsp := by rw [rg5 a0, g4_10]
  have g5_11 : reg n5 a1 = tsl := by rw [rg5 a1, g4_11]
  have g5_12 : reg n5 a2 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by rw [rg5 a2, g4_12]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [rg5 (18 : Fin 32), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [rg5 (19 : Fin 32), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [rg5 (20 : Fin 32), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [rg5 (21 : Fin 32), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [rg5 (22 : Fin 32), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [rg5 (23 : Fin 32), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [rg5 (24 : Fin 32), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [rg5 (25 : Fin 32), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [rg5 (26 : Fin 32), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [rg5 (27 : Fin 32), g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x2D0, 0x4)] := keep_kk4.trans K5.toL
  clear keep_kk4
  have w5_2d0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [W5, g4_10]
  clear g4_12 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_11 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0xA6A: sw
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := sv_sw F E5 s5 sv_at_a6a (off' := 0xA6C) (c := 0x2D4)
    (by decide) (by rw [g5_12]; sv_addr) (by decide) (by decide)
  have t6 : Steps n0 n6 := t5.trans d6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rg6 sp, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg6 (3 : Fin 32), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg6 (4 : Fin 32), g5_4]
  have g6_10 : reg n6 a0 = tsp := by rw [rg6 a0, g5_10]
  have g6_11 : reg n6 a1 = tsl := by rw [rg6 a1, g5_11]
  have g6_12 : reg n6 a2 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by rw [rg6 a2, g5_12]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [rg6 (18 : Fin 32), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [rg6 (19 : Fin 32), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [rg6 (20 : Fin 32), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [rg6 (21 : Fin 32), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [rg6 (22 : Fin 32), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [rg6 (23 : Fin 32), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [rg6 (24 : Fin 32), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [rg6 (25 : Fin 32), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [rg6 (26 : Fin 32), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by rw [rg6 (27 : Fin 32), g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x2D0, 0x4), (0x2D4, 0x4)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_2d0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K6.w32 (by decide) (by decide)).trans w5_2d0
  have w6_2d4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [W6, g5_11]
  clear w5_2d0 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_12 g5_11 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 rg5 W5 K5 fr5 s5 d5
  -- 0xA6C: sw
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := sv_sw F E6 s6 sv_at_a6c (off' := 0xA6E) (c := 0x2D8)
    (by decide) (by rw [g6_12]; sv_addr) (by decide) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_10 : reg n7 a0 = tsp := by rw [rg7 a0, g6_10]
  have g7_11 : reg n7 a1 = tsl := by rw [rg7 a1, g6_11]
  have g7_12 : reg n7 a2 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by rw [rg7 a2, g6_12]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rg7 (18 : Fin 32), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rg7 (19 : Fin 32), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [rg7 (20 : Fin 32), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [rg7 (21 : Fin 32), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [rg7 (22 : Fin 32), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [rg7 (23 : Fin 32), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [rg7 (24 : Fin 32), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [rg7 (25 : Fin 32), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [rg7 (26 : Fin 32), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [rg7 (27 : Fin 32), g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_2d0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K7.w32 (by decide) (by decide)).trans w6_2d0
  have w7_2d4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K7.w32 (by decide) (by decide)).trans w6_2d4
  have w7_2d8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = tsp := by rw [W7, g6_10]
  clear w6_2d4 w6_2d0 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_12 g6_11 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
  -- 0xA6E: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_a6e (off' := 0xA70) (c := 0x2DC)
    (by decide) (by rw [g7_12]; sv_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_10 : reg n8 a0 = tsp := by rw [rg8 a0, g7_10]
  have g8_11 : reg n8 a1 = tsl := by rw [rg8 a1, g7_11]
  have g8_12 : reg n8 a2 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by rw [rg8 a2, g7_12]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [rg8 (20 : Fin 32), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [rg8 (22 : Fin 32), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [rg8 (23 : Fin 32), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [rg8 (26 : Fin 32), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by rw [rg8 (27 : Fin 32), g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_2d0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K8.w32 (by decide) (by decide)).trans w7_2d0
  have w8_2d4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K8.w32 (by decide) (by decide)).trans w7_2d4
  have w8_2d8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = tsp := (K8.w32 (by decide) (by decide)).trans w7_2d8
  have w8_2dc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = tsl := by rw [W8, g7_11]
  clear w7_2d8 w7_2d4 w7_2d0 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_12 g7_11 g7_10 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0xA70
  obtain ⟨n9, c9, u9⟩ := s8.block svTr1a70 E8.self svTr1a70_end
    ⟨trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0xA76 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svTr1a70 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_12 : reg n9 a2 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by
    rw [rb9, runBlock_reg _ _ _ a2 s8.zero (by decide), g8_12]
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
  have g9_10 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svTr1a70, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_10, g8_11, g8_12, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g9_11 : reg n9 a1 = B + 0x21A0 + BitVec.ofNat 32 0x2D0 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svTr1a70, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_10, g8_11, g8_12, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_2d0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m9]; exact w8_2d0
  have w9_2d4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m9]; exact w8_2d4
  have w9_2d8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = tsp := by rw [m9]; exact w8_2d8
  have w9_2dc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = tsl := by rw [m9]; exact w8_2dc
  clear w8_2dc w8_2d8 w8_2d4 w8_2d0 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_12 g8_11 g8_10 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0xA76: sv_seqF
  obtain ⟨n10, c10, s10, sp10, rk10, K10, Ok10, Er10, fr10⟩ := sv_seqF (oc := 0x420) (dc := 0x2D0)
    F E9 s9 sv_at_a76 sv_at_a7a (by decide) (by decide) g9_2 g9_10 g9_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w9_2d8 w9_2dc ts_in
  have t10 : Steps n0 n10 := t9.trans c10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keepL K10 (by decide)
  rw [sv_mb fR9 ts_in] at Ok10 Er10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rk10 sp (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk10 (3 : Fin 32) (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk10 (4 : Fin 32) (by decide) (by decide), g9_4]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rk10 (18 : Fin 32) (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rk10 (19 : Fin 32) (by decide) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [rk10 (20 : Fin 32) (by decide) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [rk10 (21 : Fin 32) (by decide) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [rk10 (22 : Fin 32) (by decide) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [rk10 (23 : Fin 32) (by decide) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [rk10 (24 : Fin 32) (by decide) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [rk10 (25 : Fin 32) (by decide) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [rk10 (26 : Fin 32) (by decide) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [rk10 (27 : Fin 32) (by decide) (by decide), g9_27]
  obtain ⟨r10, hr10⟩ : ∃ r, derElement 0x30 (memBytes M0 (tsp) (tsl).toNat) = r := ⟨_, rfl⟩
  rcases r10 with er10 | tl10
  · obtain ⟨z10, -⟩ := Er10 er10 hr10
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8)] := keep_kk9.trans K10
    clear keep_kk9
    have w10_2d0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K10.w32 (by decide) (by decide)).trans w9_2d0
    have w10_2d4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K10.w32 (by decide) (by decide)).trans w9_2d4
    have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z10
    clear w9_2dc w9_2d8 w9_2d4 w9_2d0 g9_11 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_12 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
    -- 0xA7E: lw
    obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_a7e (off' := 0xA82) (by decide)
      (by rw [g10_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s11 : St n11.mem SV n11 0xA82 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
    have g11_9 : reg n11 (9 : Fin 32) = 0 := by
      rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g10_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w10_420]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_2d0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m11]; exact w10_2d0
    have w11_2d4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m11]; exact w10_2d4
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m11]; exact w10_420
    clear w10_420 w10_2d4 w10_2d0 z10
    -- 0xA82: lbu
    obtain ⟨n12, d12, u12⟩ := s11.lbu E11.self sv_at_a82 (off' := 0xA86) (by decide)
    have s12 : St n12.mem SV n12 0xA86 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
    have g12_9 : reg n12 (9 : Fin 32) = 0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_2d0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m12]; exact w11_2d0
    have w12_2d4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m12]; exact w11_2d4
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m12]; exact w11_420
    clear w11_420 w11_2d4 w11_2d0 g11_9 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    -- 0xA86: branch, taken
    obtain ⟨n13, d13, u13⟩ := s12.taken E12.self 0x7A4 sv_at_a86
      (by decide) (by rw [g12_9, s12.zero]; rfl)
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
    have g13_9 : reg n13 (9 : Fin 32) = 0 := by rw [u13.regs, g12_9]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, g12_27]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_2d0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m13]; exact w12_2d0
    have w13_2d4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m13]; exact w12_2d4
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m13]; exact w12_420
    clear w12_420 w12_2d4 w12_2d0 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    exact .inl ⟨(fun ⟨tl10', h0', _⟩ => by rw [hr10] at h0'; cases h0'), sv_fail F E13 s13 t13 (fun x hx => (fR13 x hx).trans (fM x hx).symm) V13 hret g13_2 g13_18 hO g13_3 g13_4⟩
  obtain ⟨o0_10, o4_10, o8_10, o12_10, d8_10, d12_10⟩ := Ok10 tl10 hr10
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8)] := keep_kk9.trans K10
  clear keep_kk9
  have w10_2d0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K10.w32 (by decide) (by decide)).trans w9_2d0
  have w10_2d4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K10.w32 (by decide) (by decide)).trans w9_2d4
  have w10_2d8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := d8_10
  have w10_2dc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := d12_10
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := o0_10
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := o4_10
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := o8_10
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := o12_10
  clear w9_2dc w9_2d8 w9_2d4 w9_2d0 g9_11 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_12 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0xA7E: lw
  obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_a7e (off' := 0xA82) (by decide)
    (by rw [g10_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s11 : St n11.mem SV n11 0xA82 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
  have g11_9 : reg n11 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g10_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w10_420]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_2d0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m11]; exact w10_2d0
  have w11_2d4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m11]; exact w10_2d4
  have w11_2d8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m11]; exact w10_2d8
  have w11_2dc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m11]; exact w10_2dc
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m11]; exact w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m11]; exact w10_42c
  clear w10_42c w10_428 w10_424 w10_420 w10_2dc w10_2d8 w10_2d4 w10_2d0 d12_10 d8_10 o12_10 o8_10 o4_10 o0_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 Er10 Ok10 K10 rk10 sp10 s10 c10
  -- 0xA82: lbu
  obtain ⟨n12, d12, u12⟩ := s11.lbu E11.self sv_at_a82 (off' := 0xA86) (by decide)
  have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by
    have h := byte_of_ld w11_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s12 : St n12.mem SV n12 0xA86 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_9 : reg n12 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_8 : reg n12 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b11_424]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_2d0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m12]; exact w11_2d0
  have w12_2d4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m12]; exact w11_2d4
  have w12_2d8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m12]; exact w11_2d8
  have w12_2dc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m12]; exact w11_2dc
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m12]; exact w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m12]; exact w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m12]; exact w11_42c
  have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m12]; exact b11_424
  clear w11_42c w11_428 w11_424 w11_420 w11_2dc w11_2d8 w11_2d4 w11_2d0 g11_9 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0xA86: branch, not taken
  obtain ⟨n13, d13, u13⟩ := s12.notTaken E12.self 0xA8A sv_at_a86
    (by decide) (by rw [g12_9, s12.zero]; exact br_beq_f (ts_in.ok_ne hr10))
  have s13 : St n13.mem SV n13 0xA8A (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [u13.regs, g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [u13.regs, g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, g12_27]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_2d0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m13]; exact w12_2d0
  have w13_2d4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m13]; exact w12_2d4
  have w13_2d8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m13]; exact w12_2d8
  have w13_2dc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m13]; exact w12_2dc
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m13]; exact w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m13]; exact w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m13]; exact w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m13]; exact w12_42c
  have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m13]; exact b12_424
  clear b12_424 w12_42c w12_428 w12_424 w12_420 w12_2dc w12_2d8 w12_2d4 w12_2d0 g12_8 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 b11_424 u12 d12
  -- 0xA8A
  obtain ⟨n14, c14, u14⟩ := s13.block svTr1a8a E13.self svTr1a8a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem SV n14 0xA94 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock svTr1a8a (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_8 : reg n14 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by
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
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0x2E5 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTr1a8a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g14_11 : reg n14 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTr1a8a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g14_12 : reg n14 a2 = BitVec.ofNat 32 0xB := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTr1a8a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_2d0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m14]; exact w13_2d0
  have w14_2d4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m14]; exact w13_2d4
  have w14_2d8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m14]; exact w13_2d8
  have w14_2dc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m14]; exact w13_2dc
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m14]; exact w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m14]; exact w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m14]; exact w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m14]; exact w13_42c
  have b14_424 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m14]; exact b13_424
  clear b13_424 w13_42c w13_428 w13_424 w13_420 w13_2dc w13_2d8 w13_2d4 w13_2d0 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  have b14_425 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by
    have h := byte_of_ld w14_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b14_426 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by
    have h := byte_of_ld w14_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b14_427 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by
    have h := byte_of_ld w14_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0xA94: memcpy
  obtain ⟨n15, P15, K15, X15⟩ := sv_mc (c := 0x2E5) (d := 0x425) (N := 0xB) F E14 s14 sv_at_a94 sv_at_a98
    (by decide) (by decide) g14_2 g14_10 g14_11 g14_12
    (by decide) (by decide) (by decide)
  have s15 := P15.st
  have fr15 := P15.fr
  have t15 : Steps n0 n15 := t14.trans P15.steps
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [P15.regs sp (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P15.regs (3 : Fin 32) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P15.regs (4 : Fin 32) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [P15.regs (8 : Fin 32) (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [P15.regs (9 : Fin 32) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [P15.regs (18 : Fin 32) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [P15.regs (19 : Fin 32) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [P15.regs (20 : Fin 32) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [P15.regs (21 : Fin 32) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [P15.regs (22 : Fin 32) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [P15.regs (23 : Fin 32) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [P15.regs (24 : Fin 32) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [P15.regs (25 : Fin 32) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [P15.regs (26 : Fin 32) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [P15.regs (27 : Fin 32) (by decide), g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_2d0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K15.w32 (by decide) (by decide)).trans w14_2d0
  have w15_2d4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K15.w32 (by decide) (by decide)).trans w14_2d4
  have w15_2d8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K15.w32 (by decide) (by decide)).trans w14_2d8
  have w15_2dc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K15.w32 (by decide) (by decide)).trans w14_2dc
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := (K15.w32 (by decide) (by decide)).trans w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := (K15.w32 (by decide) (by decide)).trans w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := (K15.w32 (by decide) (by decide)).trans w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K15.w32 (by decide) (by decide)).trans w14_42c
  have b15_424 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K15.b8 (by decide) (by decide)).trans b14_424
  have b15_425 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K15.b8 (by decide) (by decide)).trans b14_425
  have b15_426 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K15.b8 (by decide) (by decide)).trans b14_426
  have b15_427 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K15.b8 (by decide) (by decide)).trans b14_427
  have w15_2e8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (tsp) + BitVec.ofNat 32 tl10.header := by
    rw [← w14_428]
    exact ld_cp fun q hq => by
      have := X15 (0x3 + q) (by omega)
      rwa [show 0x2E5 + (0x3 + q) = 0x2E8 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w15_2ec : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = BitVec.ofNat 32 tl10.len := by
    rw [← w14_42c]
    exact ld_cp fun q hq => by
      have := X15 (0x7 + q) (by omega)
      rwa [show 0x2E5 + (0x7 + q) = 0x2EC + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b15_2e5 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E5) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [show 0x2E5 = 0x2E5 + 0x0 from rfl, X15 0x0 (by decide)]; exact b14_425
  have b15_2e6 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E6) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [show 0x2E6 = 0x2E5 + 0x1 from rfl, X15 0x1 (by decide)]; exact b14_426
  have b15_2e7 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E7) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [show 0x2E7 = 0x2E5 + 0x2 from rfl, X15 0x2 (by decide)]; exact b14_427
  clear b14_424 w14_42c w14_428 w14_424 w14_420 w14_2dc w14_2d8 w14_2d4 w14_2d0 g14_12 g14_11 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0xA9C: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_a9c (off' := 0xAA0) (by decide)
    (by rw [g15_2, show B + 0x21A0 + 0x2DC = B + 0x21A0 + BitVec.ofNat 32 0x2DC by sv_addr]; exact sv_al F (by decide) (by decide))
  have s16 : St n16.mem SV n16 0xAA0 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
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
  have g16_10 : reg n16 a0 = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_2, show B + 0x21A0 + 0x2DC = B + 0x21A0 + BitVec.ofNat 32 0x2DC by sv_addr, w15_2dc]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_2d0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m16]; exact w15_2d0
  have w16_2d4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m16]; exact w15_2d4
  have w16_2d8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m16]; exact w15_2d8
  have w16_2dc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m16]; exact w15_2dc
  have w16_2e8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m16]; exact w15_2e8
  have w16_2ec : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = BitVec.ofNat 32 tl10.len := by rw [m16]; exact w15_2ec
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m16]; exact w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m16]; exact w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m16]; exact w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m16]; exact w15_42c
  have b16_2e5 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E5) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m16]; exact b15_2e5
  have b16_2e6 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E6) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m16]; exact b15_2e6
  have b16_2e7 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E7) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m16]; exact b15_2e7
  have b16_424 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m16]; exact b15_424
  have b16_425 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m16]; exact b15_425
  have b16_426 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m16]; exact b15_426
  have b16_427 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m16]; exact b15_427
  clear b15_2e7 b15_2e6 b15_2e5 w15_2ec w15_2e8 b15_427 b15_426 b15_425 b15_424 w15_42c w15_428 w15_424 w15_420 w15_2dc w15_2d8 w15_2d4 w15_2d0 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 s15 X15 K15 P15 b14_427 b14_426 b14_425
  -- 0xAA0: sw
  obtain ⟨n17, d17, s17, fr17, K17, W17, rg17⟩ := sv_sw F E16 s16 sv_at_aa0 (off' := 0xAA4) (c := 0x2E0)
    (by decide) (by rw [g16_2]; sv_addr) (by decide) (by decide)
  have t17 : Steps n0 n17 := t16.trans d17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rg17 sp, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg17 (3 : Fin 32), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg17 (4 : Fin 32), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg17 (8 : Fin 32), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [rg17 (9 : Fin 32), g16_9]
  have g17_10 : reg n17 a0 = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [rg17 a0, g16_10]
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
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_2d0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K17.w32 (by decide) (by decide)).trans w16_2d0
  have w17_2d4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K17.w32 (by decide) (by decide)).trans w16_2d4
  have w17_2d8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K17.w32 (by decide) (by decide)).trans w16_2d8
  have w17_2dc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K17.w32 (by decide) (by decide)).trans w16_2dc
  have w17_2e8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (tsp) + BitVec.ofNat 32 tl10.header := (K17.w32 (by decide) (by decide)).trans w16_2e8
  have w17_2ec : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = BitVec.ofNat 32 tl10.len := (K17.w32 (by decide) (by decide)).trans w16_2ec
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := (K17.w32 (by decide) (by decide)).trans w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := (K17.w32 (by decide) (by decide)).trans w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := (K17.w32 (by decide) (by decide)).trans w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K17.w32 (by decide) (by decide)).trans w16_42c
  have b17_2e5 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E5) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K17.b8 (by decide) (by decide)).trans b16_2e5
  have b17_2e6 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E6) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K17.b8 (by decide) (by decide)).trans b16_2e6
  have b17_2e7 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E7) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K17.b8 (by decide) (by decide)).trans b16_2e7
  have b17_424 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K17.b8 (by decide) (by decide)).trans b16_424
  have b17_425 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K17.b8 (by decide) (by decide)).trans b16_425
  have b17_426 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K17.b8 (by decide) (by decide)).trans b16_426
  have b17_427 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K17.b8 (by decide) (by decide)).trans b16_427
  have w17_2e0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [W17, g16_9]
  clear b16_427 b16_426 b16_425 b16_424 b16_2e7 b16_2e6 b16_2e5 w16_42c w16_428 w16_424 w16_420 w16_2ec w16_2e8 w16_2dc w16_2d8 w16_2d4 w16_2d0 g16_10 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0xAA4: sb
  obtain ⟨n18, d18, s18, fr18, K18, W18, rg18⟩ := sv_sb F E17 s17 sv_at_aa4 (off' := 0xAA8) (c := 0x2E4)
    (by decide) (by rw [g17_2]; sv_addr) (by decide)
  have t18 : Steps n0 n18 := t17.trans d18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [rg18 sp, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg18 (3 : Fin 32), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg18 (4 : Fin 32), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg18 (8 : Fin 32), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [rg18 (9 : Fin 32), g17_9]
  have g18_10 : reg n18 a0 = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [rg18 a0, g17_10]
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
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_2d0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K18.w32 (by decide) (by decide)).trans w17_2d0
  have w18_2d4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K18.w32 (by decide) (by decide)).trans w17_2d4
  have w18_2d8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K18.w32 (by decide) (by decide)).trans w17_2d8
  have w18_2dc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K18.w32 (by decide) (by decide)).trans w17_2dc
  have w18_2e0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := (K18.w32 (by decide) (by decide)).trans w17_2e0
  have w18_2e8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (tsp) + BitVec.ofNat 32 tl10.header := (K18.w32 (by decide) (by decide)).trans w17_2e8
  have w18_2ec : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = BitVec.ofNat 32 tl10.len := (K18.w32 (by decide) (by decide)).trans w17_2ec
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := (K18.w32 (by decide) (by decide)).trans w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := (K18.w32 (by decide) (by decide)).trans w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := (K18.w32 (by decide) (by decide)).trans w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K18.w32 (by decide) (by decide)).trans w17_42c
  have b18_2e5 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E5) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K18.b8 (by decide) (by decide)).trans b17_2e5
  have b18_2e6 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E6) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K18.b8 (by decide) (by decide)).trans b17_2e6
  have b18_2e7 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E7) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K18.b8 (by decide) (by decide)).trans b17_2e7
  have b18_424 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_424
  have b18_425 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K18.b8 (by decide) (by decide)).trans b17_425
  have b18_426 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K18.b8 (by decide) (by decide)).trans b17_426
  have b18_427 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K18.b8 (by decide) (by decide)).trans b17_427
  have b18_2e4 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [W18, g17_8, lbu_low]
  clear w17_2e0 b17_427 b17_426 b17_425 b17_424 b17_2e7 b17_2e6 b17_2e5 w17_42c w17_428 w17_424 w17_420 w17_2ec w17_2e8 w17_2dc w17_2d8 w17_2d4 w17_2d0 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
  have w18_2e4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := ld_of_bytes b18_2e4
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x2E4 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x2E5 by sv_addr]; exact b18_2e5)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x2E4 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x2E6 by sv_addr]; exact b18_2e6)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x2E4 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x2E7 by sv_addr]; exact b18_2e7)
  by_cases hrem : (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) = 0
  rotate_left
  · -- 0xAA8: branch, taken
    obtain ⟨n19, d19, u19⟩ := s18.taken E18.self 0x14C sv_at_aa8
      (by decide) (by rw [g18_10, s18.zero]; exact br_bne_t hrem)
    have s19 : St n19.mem SV n19 0x14C (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
    have g19_8 : reg n19 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [u19.regs, g18_8]
    have g19_9 : reg n19 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [u19.regs, g18_9]
    have g19_10 : reg n19 a0 = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [u19.regs, g18_10]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [u19.regs, g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [u19.regs, g18_27]
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_2d0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m19]; exact w18_2d0
    have w19_2d4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m19]; exact w18_2d4
    have w19_2d8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m19]; exact w18_2d8
    have w19_2dc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m19]; exact w18_2dc
    have w19_2e0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m19]; exact w18_2e0
    have w19_2e4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m19]; exact w18_2e4
    have w19_2e8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m19]; exact w18_2e8
    have w19_2ec : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = BitVec.ofNat 32 tl10.len := by rw [m19]; exact w18_2ec
    have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m19]; exact w18_420
    have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m19]; exact w18_424
    have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m19]; exact w18_428
    have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m19]; exact w18_42c
    have b19_424 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m19]; exact b18_424
    have b19_425 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m19]; exact b18_425
    have b19_426 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m19]; exact b18_426
    have b19_427 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m19]; exact b18_427
    clear b18_2e4 b18_427 b18_426 b18_425 b18_424 b18_2e7 b18_2e6 b18_2e5 w18_42c w18_428 w18_424 w18_420 w18_2ec w18_2e8 w18_2e0 w18_2dc w18_2d8 w18_2d4 w18_2d0 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 rg18 W18 K18 fr18 s18 d18
    -- 0x14C
    obtain ⟨n20, c20, u20⟩ := s19.block svTr114c E19.self svTr114c_end
      ⟨trivial, trivial⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have s20 : St n20.mem SV n20 0x14E (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have rb20 : ∀ q, reg n20 q = (runBlock svTr114c (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
    have g20_9 : reg n20 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by
      rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
    have g20_10 : reg n20 a0 = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by
      rw [rb20, runBlock_reg _ _ _ a0 s19.zero (by decide), g19_10]
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
      rw [rb20]; simp +decide only [runBlock, BInstr.run, svTr114c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_2d0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m20]; exact w19_2d0
    have w20_2d4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m20]; exact w19_2d4
    have w20_2d8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m20]; exact w19_2d8
    have w20_2dc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m20]; exact w19_2dc
    have w20_2e0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_2e0
    have w20_2e4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m20]; exact w19_2e4
    have w20_2e8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_2e8
    have w20_2ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = BitVec.ofNat 32 tl10.len := by rw [m20]; exact w19_2ec
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_420
    have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m20]; exact w19_424
    have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_428
    have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m20]; exact w19_42c
    have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m20]; exact b19_424
    have b20_425 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m20]; exact b19_425
    have b20_426 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m20]; exact b19_426
    have b20_427 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m20]; exact b19_427
    clear b19_427 b19_426 b19_425 b19_424 w19_42c w19_428 w19_424 w19_420 w19_2ec w19_2e8 w19_2e4 w19_2e0 w19_2dc w19_2d8 w19_2d4 w19_2d0 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
    -- 0x14E: j
    obtain ⟨n21, d21, u21⟩ := s20.jump E20.self sv_at_14e (off' := 0x7A4) (by decide)
      (by rw [s20.pc]; decide)
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
    have g21_9 : reg n21 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [u21.regs, g20_9]
    have g21_10 : reg n21 a0 = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [u21.regs, g20_10]
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
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_2d0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m21]; exact w20_2d0
    have w21_2d4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m21]; exact w20_2d4
    have w21_2d8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m21]; exact w20_2d8
    have w21_2dc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m21]; exact w20_2dc
    have w21_2e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m21]; exact w20_2e0
    have w21_2e4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m21]; exact w20_2e4
    have w21_2e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m21]; exact w20_2e8
    have w21_2ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = BitVec.ofNat 32 tl10.len := by rw [m21]; exact w20_2ec
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m21]; exact w20_420
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m21]; exact w20_424
    have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m21]; exact w20_428
    have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m21]; exact w20_42c
    have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m21]; exact b20_424
    have b21_425 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m21]; exact b20_425
    have b21_426 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m21]; exact b20_426
    have b21_427 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m21]; exact b20_427
    clear b20_427 b20_426 b20_425 b20_424 w20_42c w20_428 w20_424 w20_420 w20_2ec w20_2e8 w20_2e4 w20_2e0 w20_2dc w20_2d8 w20_2d4 w20_2d0 g20_8 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
    exact .inl ⟨(fun ⟨tl10', h0', h1', _⟩ => by rw [hr10] at h0'; cases h0'; exact hrem h1'), sv_fail F E21 s21 t21 (fun x hx => (fR21 x hx).trans (fM x hx).symm) V21 hret g21_2 g21_18 hO g21_3 g21_4⟩
  -- 0xAA8: branch, not taken
  obtain ⟨n19, d19, u19⟩ := s18.notTaken E18.self 0xAAC sv_at_aa8
    (by decide) (by rw [g18_10, s18.zero]; exact br_bne_f hrem)
  have s19 : St n19.mem SV n19 0xAAC (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [u19.regs, g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [u19.regs, g18_9]
  have g19_10 : reg n19 a0 = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [u19.regs, g18_10]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [u19.regs, g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [u19.regs, g18_27]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_2d0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m19]; exact w18_2d0
  have w19_2d4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m19]; exact w18_2d4
  have w19_2d8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m19]; exact w18_2d8
  have w19_2dc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m19]; exact w18_2dc
  have w19_2e0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m19]; exact w18_2e0
  have w19_2e4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m19]; exact w18_2e4
  have w19_2e8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m19]; exact w18_2e8
  have w19_2ec : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = BitVec.ofNat 32 tl10.len := by rw [m19]; exact w18_2ec
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m19]; exact w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m19]; exact w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m19]; exact w18_42c
  have b19_424 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m19]; exact b18_424
  have b19_425 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m19]; exact b18_425
  have b19_426 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m19]; exact b18_426
  have b19_427 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m19]; exact b18_427
  clear b18_2e4 b18_427 b18_426 b18_425 b18_424 b18_2e7 b18_2e6 b18_2e5 w18_42c w18_428 w18_424 w18_420 w18_2ec w18_2e8 w18_2e0 w18_2dc w18_2d8 w18_2d4 w18_2d0 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 rg18 W18 K18 fr18 s18 d18
  -- 0xAAC
  obtain ⟨n20, c20, u20⟩ := s19.block svTr1aac E19.self svTr1aac_end
    ⟨trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0xAB2 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svTr1aac (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
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
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svTr1aac, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_11 : reg n20 a1 = B + 0x21A0 + BitVec.ofNat 32 0x2E0 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svTr1aac, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_2d0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m20]; exact w19_2d0
  have w20_2d4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m20]; exact w19_2d4
  have w20_2d8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m20]; exact w19_2d8
  have w20_2dc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m20]; exact w19_2dc
  have w20_2e0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_2e0
  have w20_2e4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m20]; exact w19_2e4
  have w20_2e8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_2e8
  have w20_2ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = BitVec.ofNat 32 tl10.len := by rw [m20]; exact w19_2ec
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m20]; exact w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m20]; exact w19_42c
  have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m20]; exact b19_424
  have b20_425 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m20]; exact b19_425
  have b20_426 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m20]; exact b19_426
  have b20_427 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m20]; exact b19_427
  clear b19_427 b19_426 b19_425 b19_424 w19_42c w19_428 w19_424 w19_420 w19_2ec w19_2e8 w19_2e4 w19_2e0 w19_2dc w19_2d8 w19_2d4 w19_2d0 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19 w18_2e4
  -- 0xAB2: sv_seqF
  obtain ⟨n21, c21, s21, sp21, rk21, K21, Ok21, Er21, fr21⟩ := sv_seqF (oc := 0x420) (dc := 0x2E0)
    F E20 s20 sv_at_ab2 sv_at_ab6 (by decide) (by decide) g20_2 g20_10 g20_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w20_2e8 w20_2ec (ts_in.contentW hr10)
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keepL K21 (by decide)
  rw [sv_mb fR20 (ts_in.contentW hr10)] at Ok21 Er21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rk21 sp (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk21 (3 : Fin 32) (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk21 (4 : Fin 32) (by decide) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk21 (8 : Fin 32) (by decide) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [rk21 (9 : Fin 32) (by decide) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rk21 (18 : Fin 32) (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rk21 (19 : Fin 32) (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [rk21 (20 : Fin 32) (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [rk21 (21 : Fin 32) (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [rk21 (22 : Fin 32) (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [rk21 (23 : Fin 32) (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [rk21 (24 : Fin 32) (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [rk21 (25 : Fin 32) (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [rk21 (26 : Fin 32) (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [rk21 (27 : Fin 32) (by decide) (by decide), g20_27]
  obtain ⟨r21, hr21⟩ : ∃ r, derElement 0x30 (memBytes M0 ((tsp) + BitVec.ofNat 32 tl10.header) (BitVec.ofNat 32 tl10.len).toNat) = r := ⟨_, rfl⟩
  rcases r21 with er21 | tl21
  · obtain ⟨z21, -⟩ := Er21 er21 hr21
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8)] := keep_kk20.trans K21
    clear keep_kk20
    have w21_2d0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K21.w32 (by decide) (by decide)).trans w20_2d0
    have w21_2d4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K21.w32 (by decide) (by decide)).trans w20_2d4
    have w21_2d8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K21.w32 (by decide) (by decide)).trans w20_2d8
    have w21_2dc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K21.w32 (by decide) (by decide)).trans w20_2dc
    have w21_2e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := (K21.w32 (by decide) (by decide)).trans w20_2e0
    have w21_2e4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := (K21.w32 (by decide) (by decide)).trans w20_2e4
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z21
    clear b20_427 b20_426 b20_425 b20_424 w20_42c w20_428 w20_424 w20_420 w20_2ec w20_2e8 w20_2e4 w20_2e0 w20_2dc w20_2d8 w20_2d4 w20_2d0 g20_11 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
    -- 0xABA: lw
    obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_aba (off' := 0xABE) (by decide)
      (by rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s22 : St n22.mem SV n22 0xABE (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = x24 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
    have g22_9 : reg n22 (9 : Fin 32) = 0 := by
      rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w21_420]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_2d0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m22]; exact w21_2d0
    have w22_2d4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m22]; exact w21_2d4
    have w22_2d8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m22]; exact w21_2d8
    have w22_2dc : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m22]; exact w21_2dc
    have w22_2e0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m22]; exact w21_2e0
    have w22_2e4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m22]; exact w21_2e4
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m22]; exact w21_420
    clear w21_420 w21_2e4 w21_2e0 w21_2dc w21_2d8 w21_2d4 w21_2d0 z21
    -- 0xABE: lbu
    obtain ⟨n23, d23, u23⟩ := s22.lbu E22.self sv_at_abe (off' := 0xAC2) (by decide)
    have s23 : St n23.mem SV n23 0xAC2 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
    have t23 : Steps n0 n23 := t22.trans (.single d23)
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.same m23
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
    have g23_9 : reg n23 (9 : Fin 32) = 0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
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
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_2d0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m23]; exact w22_2d0
    have w23_2d4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m23]; exact w22_2d4
    have w23_2d8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m23]; exact w22_2d8
    have w23_2dc : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m23]; exact w22_2dc
    have w23_2e0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m23]; exact w22_2e0
    have w23_2e4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m23]; exact w22_2e4
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m23]; exact w22_420
    clear w22_420 w22_2e4 w22_2e0 w22_2dc w22_2d8 w22_2d4 w22_2d0 g22_9 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    -- 0xAC2: branch, taken
    obtain ⟨n24, d24, u24⟩ := s23.taken E23.self 0x7A4 sv_at_ac2
      (by decide) (by rw [g23_9, s23.zero]; rfl)
    have s24 : St n24.mem SV n24 0x7A4 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
    have g24_9 : reg n24 (9 : Fin 32) = 0 := by rw [u24.regs, g23_9]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = x24 := by rw [u24.regs, g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [u24.regs, g23_27]
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_2d0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m24]; exact w23_2d0
    have w24_2d4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m24]; exact w23_2d4
    have w24_2d8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m24]; exact w23_2d8
    have w24_2dc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m24]; exact w23_2dc
    have w24_2e0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m24]; exact w23_2e0
    have w24_2e4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m24]; exact w23_2e4
    have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m24]; exact w23_420
    clear w23_420 w23_2e4 w23_2e0 w23_2dc w23_2d8 w23_2d4 w23_2d0 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
    exact .inl ⟨(fun ⟨tl10', h0', h1', tl21', h2', _⟩ => by rw [hr10] at h0'; cases h0'; rw [hr21] at h2'; cases h2'), sv_fail F E24 s24 t24 (fun x hx => (fR24 x hx).trans (fM x hx).symm) V24 hret g24_2 g24_18 hO g24_3 g24_4⟩
  obtain ⟨o0_21, o4_21, o8_21, o12_21, d8_21, d12_21⟩ := Ok21 tl21 hr21
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8)] := keep_kk20.trans K21
  clear keep_kk20
  have w21_2d0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K21.w32 (by decide) (by decide)).trans w20_2d0
  have w21_2d4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K21.w32 (by decide) (by decide)).trans w20_2d4
  have w21_2d8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K21.w32 (by decide) (by decide)).trans w20_2d8
  have w21_2dc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K21.w32 (by decide) (by decide)).trans w20_2dc
  have w21_2e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := (K21.w32 (by decide) (by decide)).trans w20_2e0
  have w21_2e4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := (K21.w32 (by decide) (by decide)).trans w20_2e4
  have w21_2e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := d8_21
  have w21_2ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := d12_21
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := o0_21
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := o4_21
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := o8_21
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := o12_21
  clear b20_427 b20_426 b20_425 b20_424 w20_42c w20_428 w20_424 w20_420 w20_2ec w20_2e8 w20_2e4 w20_2e0 w20_2dc w20_2d8 w20_2d4 w20_2d0 g20_11 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0xABA: lw
  obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_aba (off' := 0xABE) (by decide)
    (by rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s22 : St n22.mem SV n22 0xABE (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = x24 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
  have g22_9 : reg n22 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by
    rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w21_420]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_2d0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m22]; exact w21_2d0
  have w22_2d4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m22]; exact w21_2d4
  have w22_2d8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m22]; exact w21_2d8
  have w22_2dc : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m22]; exact w21_2dc
  have w22_2e0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m22]; exact w21_2e0
  have w22_2e4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m22]; exact w21_2e4
  have w22_2e8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m22]; exact w21_2e8
  have w22_2ec : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m22]; exact w21_2ec
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m22]; exact w21_42c
  clear w21_42c w21_428 w21_424 w21_420 w21_2ec w21_2e8 w21_2e4 w21_2e0 w21_2dc w21_2d8 w21_2d4 w21_2d0 d12_21 d8_21 o12_21 o8_21 o4_21 o0_21 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 Er21 Ok21 K21 rk21 sp21 s21 c21
  -- 0xABE: lbu
  obtain ⟨n23, d23, u23⟩ := s22.lbu E22.self sv_at_abe (off' := 0xAC2) (by decide)
  have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by
    have h := byte_of_ld w22_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s23 : St n23.mem SV n23 0xAC2 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_9 : reg n23 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
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
  have g23_8 : reg n23 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b22_424]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_2d0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m23]; exact w22_2d0
  have w23_2d4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m23]; exact w22_2d4
  have w23_2d8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m23]; exact w22_2d8
  have w23_2dc : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m23]; exact w22_2dc
  have w23_2e0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m23]; exact w22_2e0
  have w23_2e4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m23]; exact w22_2e4
  have w23_2e8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m23]; exact w22_2e8
  have w23_2ec : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m23]; exact w22_2ec
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m23]; exact w22_42c
  have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m23]; exact b22_424
  clear w22_42c w22_428 w22_424 w22_420 w22_2ec w22_2e8 w22_2e4 w22_2e0 w22_2dc w22_2d8 w22_2d4 w22_2d0 g22_9 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0xAC2: branch, not taken
  obtain ⟨n24, d24, u24⟩ := s23.notTaken E23.self 0xAC6 sv_at_ac2
    (by decide) (by rw [g23_9, s23.zero]; exact br_beq_f ((ts_in.contentW hr10).ok_ne hr21))
  have s24 : St n24.mem SV n24 0xAC6 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [u24.regs, g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [u24.regs, g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = x24 := by rw [u24.regs, g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [u24.regs, g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_2d0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m24]; exact w23_2d0
  have w24_2d4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m24]; exact w23_2d4
  have w24_2d8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m24]; exact w23_2d8
  have w24_2dc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m24]; exact w23_2dc
  have w24_2e0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m24]; exact w23_2e0
  have w24_2e4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m24]; exact w23_2e4
  have w24_2e8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m24]; exact w23_2e8
  have w24_2ec : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m24]; exact w23_2ec
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m24]; exact w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m24]; exact w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m24]; exact w23_42c
  have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m24]; exact b23_424
  clear b23_424 w23_42c w23_428 w23_424 w23_420 w23_2ec w23_2e8 w23_2e4 w23_2e0 w23_2dc w23_2d8 w23_2d4 w23_2d0 g23_8 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 b22_424 u23 d23
  -- 0xAC6
  obtain ⟨n25, c25, u25⟩ := s24.block svTr1ac6 E24.self svTr1ac6_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0xAD0 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svTr1ac6 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by
    rw [rb25, runBlock_reg _ _ _ sp s24.zero (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb25, runBlock_reg _ _ _ (3 : Fin 32) s24.zero (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb25, runBlock_reg _ _ _ (4 : Fin 32) s24.zero (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by
    rw [rb25, runBlock_reg _ _ _ (18 : Fin 32) s24.zero (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by
    rw [rb25, runBlock_reg _ _ _ (19 : Fin 32) s24.zero (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by
    rw [rb25, runBlock_reg _ _ _ (20 : Fin 32) s24.zero (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by
    rw [rb25, runBlock_reg _ _ _ (21 : Fin 32) s24.zero (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by
    rw [rb25, runBlock_reg _ _ _ (22 : Fin 32) s24.zero (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by
    rw [rb25, runBlock_reg _ _ _ (23 : Fin 32) s24.zero (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = x24 := by
    rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by
    rw [rb25, runBlock_reg _ _ _ (25 : Fin 32) s24.zero (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = x27 := by
    rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0x2F5 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svTr1ac6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svTr1ac6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_12 : reg n25 a2 = BitVec.ofNat 32 0xB := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svTr1ac6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_2d0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m25]; exact w24_2d0
  have w25_2d4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m25]; exact w24_2d4
  have w25_2d8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m25]; exact w24_2d8
  have w25_2dc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m25]; exact w24_2dc
  have w25_2e0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m25]; exact w24_2e0
  have w25_2e4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m25]; exact w24_2e4
  have w25_2e8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m25]; exact w24_2e8
  have w25_2ec : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m25]; exact w24_2ec
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m25]; exact w24_420
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m25]; exact w24_424
  have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m25]; exact w24_428
  have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m25]; exact w24_42c
  have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m25]; exact b24_424
  clear b24_424 w24_42c w24_428 w24_424 w24_420 w24_2ec w24_2e8 w24_2e4 w24_2e0 w24_2dc w24_2d8 w24_2d4 w24_2d0 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by
    have h := byte_of_ld w25_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by
    have h := byte_of_ld w25_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by
    have h := byte_of_ld w25_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0xAD0: memcpy
  obtain ⟨n26, P26, K26, X26⟩ := sv_mc (c := 0x2F5) (d := 0x425) (N := 0xB) F E25 s25 sv_at_ad0 sv_at_ad4
    (by decide) (by decide) g25_2 g25_10 g25_11 g25_12
    (by decide) (by decide) (by decide)
  have s26 := P26.st
  have fr26 := P26.fr
  have t26 : Steps n0 n26 := t25.trans P26.steps
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [P26.regs sp (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P26.regs (3 : Fin 32) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P26.regs (4 : Fin 32) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [P26.regs (8 : Fin 32) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [P26.regs (9 : Fin 32) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [P26.regs (18 : Fin 32) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [P26.regs (19 : Fin 32) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [P26.regs (20 : Fin 32) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [P26.regs (21 : Fin 32) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [P26.regs (22 : Fin 32) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [P26.regs (23 : Fin 32) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [P26.regs (24 : Fin 32) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [P26.regs (25 : Fin 32) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [P26.regs (26 : Fin 32) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [P26.regs (27 : Fin 32) (by decide), g25_27]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB)] := keep_kk25.trans K26.toL
  clear keep_kk25
  have w26_2d0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K26.w32 (by decide) (by decide)).trans w25_2d0
  have w26_2d4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K26.w32 (by decide) (by decide)).trans w25_2d4
  have w26_2d8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K26.w32 (by decide) (by decide)).trans w25_2d8
  have w26_2dc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K26.w32 (by decide) (by decide)).trans w25_2dc
  have w26_2e0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := (K26.w32 (by decide) (by decide)).trans w25_2e0
  have w26_2e4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := (K26.w32 (by decide) (by decide)).trans w25_2e4
  have w26_2e8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K26.w32 (by decide) (by decide)).trans w25_2e8
  have w26_2ec : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K26.w32 (by decide) (by decide)).trans w25_2ec
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K26.w32 (by decide) (by decide)).trans w25_420
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := (K26.w32 (by decide) (by decide)).trans w25_424
  have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K26.w32 (by decide) (by decide)).trans w25_428
  have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := (K26.w32 (by decide) (by decide)).trans w25_42c
  have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_424
  have b26_425 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K26.b8 (by decide) (by decide)).trans b25_425
  have b26_426 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K26.b8 (by decide) (by decide)).trans b25_426
  have b26_427 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K26.b8 (by decide) (by decide)).trans b25_427
  have w26_2f8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by
    rw [← w25_428]
    exact ld_cp fun q hq => by
      have := X26 (0x3 + q) (by omega)
      rwa [show 0x2F5 + (0x3 + q) = 0x2F8 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w26_2fc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = BitVec.ofNat 32 tl21.len := by
    rw [← w25_42c]
    exact ld_cp fun q hq => by
      have := X26 (0x7 + q) (by omega)
      rwa [show 0x2F5 + (0x7 + q) = 0x2FC + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b26_2f5 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F5) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [show 0x2F5 = 0x2F5 + 0x0 from rfl, X26 0x0 (by decide)]; exact b25_425
  have b26_2f6 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F6) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [show 0x2F6 = 0x2F5 + 0x1 from rfl, X26 0x1 (by decide)]; exact b25_426
  have b26_2f7 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F7) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [show 0x2F7 = 0x2F5 + 0x2 from rfl, X26 0x2 (by decide)]; exact b25_427
  clear b25_424 w25_42c w25_428 w25_424 w25_420 w25_2ec w25_2e8 w25_2e4 w25_2e0 w25_2dc w25_2d8 w25_2d4 w25_2d0 g25_12 g25_11 g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0xAD8: sw
  obtain ⟨n27, d27, s27, fr27, K27, W27, rg27⟩ := sv_sw F E26 s26 sv_at_ad8 (off' := 0xADC) (c := 0x2F0)
    (by decide) (by rw [g26_2]; sv_addr) (by decide) (by decide)
  have t27 : Steps n0 n27 := t26.trans d27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keep K27 (by decide)
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rg27 sp, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg27 (3 : Fin 32), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg27 (4 : Fin 32), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg27 (8 : Fin 32), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [rg27 (9 : Fin 32), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rg27 (18 : Fin 32), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rg27 (19 : Fin 32), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [rg27 (20 : Fin 32), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [rg27 (21 : Fin 32), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [rg27 (22 : Fin 32), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [rg27 (23 : Fin 32), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [rg27 (24 : Fin 32), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [rg27 (25 : Fin 32), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [rg27 (26 : Fin 32), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [rg27 (27 : Fin 32), g26_27]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4)] := keep_kk26.trans K27.toL
  clear keep_kk26
  have w27_2d0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K27.w32 (by decide) (by decide)).trans w26_2d0
  have w27_2d4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K27.w32 (by decide) (by decide)).trans w26_2d4
  have w27_2d8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K27.w32 (by decide) (by decide)).trans w26_2d8
  have w27_2dc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K27.w32 (by decide) (by decide)).trans w26_2dc
  have w27_2e0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := (K27.w32 (by decide) (by decide)).trans w26_2e0
  have w27_2e4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := (K27.w32 (by decide) (by decide)).trans w26_2e4
  have w27_2e8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K27.w32 (by decide) (by decide)).trans w26_2e8
  have w27_2ec : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K27.w32 (by decide) (by decide)).trans w26_2ec
  have w27_2f8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K27.w32 (by decide) (by decide)).trans w26_2f8
  have w27_2fc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = BitVec.ofNat 32 tl21.len := (K27.w32 (by decide) (by decide)).trans w26_2fc
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K27.w32 (by decide) (by decide)).trans w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := (K27.w32 (by decide) (by decide)).trans w26_424
  have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K27.w32 (by decide) (by decide)).trans w26_428
  have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := (K27.w32 (by decide) (by decide)).trans w26_42c
  have b27_2f5 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F5) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K27.b8 (by decide) (by decide)).trans b26_2f5
  have b27_2f6 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F6) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K27.b8 (by decide) (by decide)).trans b26_2f6
  have b27_2f7 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F7) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K27.b8 (by decide) (by decide)).trans b26_2f7
  have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_424
  have b27_425 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K27.b8 (by decide) (by decide)).trans b26_425
  have b27_426 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K27.b8 (by decide) (by decide)).trans b26_426
  have b27_427 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K27.b8 (by decide) (by decide)).trans b26_427
  have w27_2f0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [W27, g26_9]
  clear b26_2f7 b26_2f6 b26_2f5 w26_2fc w26_2f8 b26_427 b26_426 b26_425 b26_424 w26_42c w26_428 w26_424 w26_420 w26_2ec w26_2e8 w26_2e4 w26_2e0 w26_2dc w26_2d8 w26_2d4 w26_2d0 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 s26 X26 K26 P26 b25_427 b25_426 b25_425
  -- 0xADC: sb
  obtain ⟨n28, d28, s28, fr28, K28, W28, rg28⟩ := sv_sb F E27 s27 sv_at_adc (off' := 0xAE0) (c := 0x2F4)
    (by decide) (by rw [g27_2]; sv_addr) (by decide)
  have t28 : Steps n0 n28 := t27.trans d28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keep K28 (by decide)
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rg28 sp, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg28 (3 : Fin 32), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg28 (4 : Fin 32), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg28 (8 : Fin 32), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [rg28 (9 : Fin 32), g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rg28 (18 : Fin 32), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rg28 (19 : Fin 32), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [rg28 (20 : Fin 32), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [rg28 (21 : Fin 32), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [rg28 (22 : Fin 32), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [rg28 (23 : Fin 32), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [rg28 (24 : Fin 32), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [rg28 (25 : Fin 32), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [rg28 (26 : Fin 32), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [rg28 (27 : Fin 32), g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1)] := keep_kk27.trans K28.toL
  clear keep_kk27
  have w28_2d0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K28.w32 (by decide) (by decide)).trans w27_2d0
  have w28_2d4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K28.w32 (by decide) (by decide)).trans w27_2d4
  have w28_2d8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K28.w32 (by decide) (by decide)).trans w27_2d8
  have w28_2dc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K28.w32 (by decide) (by decide)).trans w27_2dc
  have w28_2e0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := (K28.w32 (by decide) (by decide)).trans w27_2e0
  have w28_2e4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := (K28.w32 (by decide) (by decide)).trans w27_2e4
  have w28_2e8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K28.w32 (by decide) (by decide)).trans w27_2e8
  have w28_2ec : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K28.w32 (by decide) (by decide)).trans w27_2ec
  have w28_2f0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K28.w32 (by decide) (by decide)).trans w27_2f0
  have w28_2f8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K28.w32 (by decide) (by decide)).trans w27_2f8
  have w28_2fc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = BitVec.ofNat 32 tl21.len := (K28.w32 (by decide) (by decide)).trans w27_2fc
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K28.w32 (by decide) (by decide)).trans w27_420
  have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := (K28.w32 (by decide) (by decide)).trans w27_424
  have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K28.w32 (by decide) (by decide)).trans w27_428
  have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := (K28.w32 (by decide) (by decide)).trans w27_42c
  have b28_2f5 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F5) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K28.b8 (by decide) (by decide)).trans b27_2f5
  have b28_2f6 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F6) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K28.b8 (by decide) (by decide)).trans b27_2f6
  have b28_2f7 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F7) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K28.b8 (by decide) (by decide)).trans b27_2f7
  have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_424
  have b28_425 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K28.b8 (by decide) (by decide)).trans b27_425
  have b28_426 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K28.b8 (by decide) (by decide)).trans b27_426
  have b28_427 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K28.b8 (by decide) (by decide)).trans b27_427
  have b28_2f4 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [W28, g27_8, lbu_low]
  clear w27_2f0 b27_427 b27_426 b27_425 b27_424 b27_2f7 b27_2f6 b27_2f5 w27_42c w27_428 w27_424 w27_420 w27_2fc w27_2f8 w27_2ec w27_2e8 w27_2e4 w27_2e0 w27_2dc w27_2d8 w27_2d4 w27_2d0 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 rg27 W27 K27 fr27 s27 d27
  have w28_2f4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := ld_of_bytes b28_2f4
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x2F4 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x2F5 by sv_addr]; exact b28_2f5)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x2F4 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x2F6 by sv_addr]; exact b28_2f6)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x2F4 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x2F7 by sv_addr]; exact b28_2f7)
  -- 0xAE0
  obtain ⟨n29, c29, u29⟩ := s28.block svTr1ae0 E28.self svTr1ae0_end
    ⟨trivial, trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem SV n29 0xAE4 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock svTr1ae0 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans c29
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by
    rw [rb29, runBlock_reg _ _ _ sp s28.zero (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb29, runBlock_reg _ _ _ (3 : Fin 32) s28.zero (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb29, runBlock_reg _ _ _ (4 : Fin 32) s28.zero (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by
    rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = out := by
    rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by
    rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by
    rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by
    rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by
    rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by
    rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = x24 := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by
    rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = x27 := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_10 : reg n29 a0 = B + 0x21A0 + BitVec.ofNat 32 0x2F0 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svTr1ae0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_11 : reg n29 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svTr1ae0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_2d0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m29]; exact w28_2d0
  have w29_2d4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m29]; exact w28_2d4
  have w29_2d8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m29]; exact w28_2d8
  have w29_2dc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m29]; exact w28_2dc
  have w29_2e0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m29]; exact w28_2e0
  have w29_2e4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m29]; exact w28_2e4
  have w29_2e8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m29]; exact w28_2e8
  have w29_2ec : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m29]; exact w28_2ec
  have w29_2f0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m29]; exact w28_2f0
  have w29_2f4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m29]; exact w28_2f4
  have w29_2f8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m29]; exact w28_2f8
  have w29_2fc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = BitVec.ofNat 32 tl21.len := by rw [m29]; exact w28_2fc
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m29]; exact w28_420
  have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m29]; exact w28_424
  have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m29]; exact w28_428
  have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m29]; exact w28_42c
  have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m29]; exact b28_424
  have b29_425 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m29]; exact b28_425
  have b29_426 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m29]; exact b28_426
  have b29_427 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m29]; exact b28_427
  clear b28_2f4 b28_427 b28_426 b28_425 b28_424 b28_2f7 b28_2f6 b28_2f5 w28_42c w28_428 w28_424 w28_420 w28_2fc w28_2f8 w28_2f0 w28_2ec w28_2e8 w28_2e4 w28_2e0 w28_2dc w28_2d8 w28_2d4 w28_2d0 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 rg28 W28 K28 fr28 s28 d28
  -- 0xAE4: sv_iiF
  obtain ⟨n30, c30, s30, sp30, rk30, K30, A30, R30, fr30⟩ := sv_iiF (dc := 0x2F0)
    F E29 s29 sv_at_ae4 sv_at_ae8 (by decide) (by decide) g29_2 g29_10
    (by decide) (by decide) w29_2f8 w29_2fc ((ts_in.contentW hr10).contentW hr21)
  have t30 : Steps n0 n30 := t29.trans c30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keepL K30 (by decide)
  rw [sv_mb fR29 ((ts_in.contentW hr10).contentW hr21), derIntIsOf_congr fR29 ((ts_in.contentW hr10).contentW hr21), g29_11] at R30
  rw [sv_mb fR29 ((ts_in.contentW hr10).contentW hr21)] at A30
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk30 (3 : Fin 32) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk30 (4 : Fin 32) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk30 (8 : Fin 32) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [rk30 (9 : Fin 32) (by decide), g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rk30 (18 : Fin 32) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rk30 (19 : Fin 32) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [rk30 (20 : Fin 32) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [rk30 (21 : Fin 32) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [rk30 (22 : Fin 32) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [rk30 (23 : Fin 32) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = x24 := by rw [rk30 (24 : Fin 32) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [rk30 (25 : Fin 32) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [rk30 (26 : Fin 32) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = x27 := by rw [rk30 (27 : Fin 32) (by decide), g29_27]
  have g30_2 : reg n30 sp = B + 0x21A0 := sp30
  obtain ⟨r30, hr30⟩ : ∃ r, derIntIsOf M0 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) (BitVec.ofNat 32 tl21.len).toNat) (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) (derElement 2 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) (BitVec.ofNat 32 tl21.len).toNat)) ((BitVec.ofNat 32 0x0).extractLsb' 0 8) = r := ⟨_, rfl⟩
  rcases r30 with b30 | (_ | _)
  · rw [hr30] at R30
    obtain ⟨a0_30, a1_30⟩ := R30
    have g30_10 : reg n30 a0 = BitVec.ofNat 32 0x1 := a0_30
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := keep_kk29.trans K30
    clear keep_kk29
    have w30_2d0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K30.w32 (by decide) (by decide)).trans w29_2d0
    have w30_2d4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K30.w32 (by decide) (by decide)).trans w29_2d4
    have w30_2d8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K30.w32 (by decide) (by decide)).trans w29_2d8
    have w30_2dc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K30.w32 (by decide) (by decide)).trans w29_2dc
    have w30_2e0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := (K30.w32 (by decide) (by decide)).trans w29_2e0
    have w30_2e4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := (K30.w32 (by decide) (by decide)).trans w29_2e4
    have w30_2e8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K30.w32 (by decide) (by decide)).trans w29_2e8
    have w30_2ec : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K30.w32 (by decide) (by decide)).trans w29_2ec
    have w30_2f0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K30.w32 (by decide) (by decide)).trans w29_2f0
    have w30_2f4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := (K30.w32 (by decide) (by decide)).trans w29_2f4
    have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K30.w32 (by decide) (by decide)).trans w29_420
    have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := (K30.w32 (by decide) (by decide)).trans w29_424
    have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K30.w32 (by decide) (by decide)).trans w29_428
    have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := (K30.w32 (by decide) (by decide)).trans w29_42c
    have b30_424 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_424
    have b30_425 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K30.b8 (by decide) (by decide)).trans b29_425
    have b30_426 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K30.b8 (by decide) (by decide)).trans b29_426
    have b30_427 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K30.b8 (by decide) (by decide)).trans b29_427
    clear b29_427 b29_426 b29_425 b29_424 w29_42c w29_428 w29_424 w29_420 w29_2fc w29_2f8 w29_2f4 w29_2f0 w29_2ec w29_2e8 w29_2e4 w29_2e0 w29_2dc w29_2d8 w29_2d4 w29_2d0 g29_11 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29 w28_2f4
    -- 0xAEC
    obtain ⟨n31, c31, u31⟩ := s30.block svTr1aec E30.self svTr1aec_end
      ⟨trivial, trivial, trivial⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have s31 : St n31.mem SV n31 0xAF0 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have rb31 : ∀ q, reg n31 q = (runBlock svTr1aec (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans c31
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by
      rw [rb31, runBlock_reg _ _ _ sp s30.zero (by decide), g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb31, runBlock_reg _ _ _ (3 : Fin 32) s30.zero (by decide), g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb31, runBlock_reg _ _ _ (4 : Fin 32) s30.zero (by decide), g30_4]
    have g31_9 : reg n31 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by
      rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
    have g31_18 : reg n31 (18 : Fin 32) = out := by
      rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by
      rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = x20 := by
      rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = x21 := by
      rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = x22 := by
      rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = x23 := by
      rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = x24 := by
      rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = x25 := by
      rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = x26 := by
      rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = x27 := by
      rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
    have g31_10 : reg n31 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb31]; simp +decide only [runBlock, BInstr.run, svTr1aec, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_2d0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m31]; exact w30_2d0
    have w31_2d4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m31]; exact w30_2d4
    have w31_2d8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m31]; exact w30_2d8
    have w31_2dc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m31]; exact w30_2dc
    have w31_2e0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m31]; exact w30_2e0
    have w31_2e4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m31]; exact w30_2e4
    have w31_2e8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m31]; exact w30_2e8
    have w31_2ec : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m31]; exact w30_2ec
    have w31_2f0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_2f0
    have w31_2f4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_2f4
    have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_420
    have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_424
    have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_428
    have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_42c
    have b31_424 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m31]; exact b30_424
    have b31_425 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m31]; exact b30_425
    have b31_426 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m31]; exact b30_426
    have b31_427 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m31]; exact b30_427
    clear b30_427 b30_426 b30_425 b30_424 w30_42c w30_428 w30_424 w30_420 w30_2f4 w30_2f0 w30_2ec w30_2e8 w30_2e4 w30_2e0 w30_2dc w30_2d8 w30_2d4 w30_2d0 g30_10 a1_30 a0_30
    -- 0xAF0: branch, taken
    obtain ⟨n32, d32, u32⟩ := s31.taken E31.self 0x7A4 sv_at_af0
      (by decide) (by rw [g31_10, s31.zero]; decide)
    have s32 : St n32.mem SV n32 0x7A4 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
    have g32_9 : reg n32 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_10]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = x24 := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = x25 := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = x27 := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_2d0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m32]; exact w31_2d0
    have w32_2d4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m32]; exact w31_2d4
    have w32_2d8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m32]; exact w31_2d8
    have w32_2dc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m32]; exact w31_2dc
    have w32_2e0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m32]; exact w31_2e0
    have w32_2e4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m32]; exact w31_2e4
    have w32_2e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m32]; exact w31_2e8
    have w32_2ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m32]; exact w31_2ec
    have w32_2f0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_2f0
    have w32_2f4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_2f4
    have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_420
    have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_424
    have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_428
    have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_42c
    have b32_424 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m32]; exact b31_424
    have b32_425 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m32]; exact b31_425
    have b32_426 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m32]; exact b31_426
    have b32_427 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m32]; exact b31_427
    clear b31_427 b31_426 b31_425 b31_424 w31_42c w31_428 w31_424 w31_420 w31_2f4 w31_2f0 w31_2ec w31_2e8 w31_2e4 w31_2e0 w31_2dc w31_2d8 w31_2d4 w31_2d0 g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
    exact .inl ⟨(fun ⟨tl10', h0', h1', tl21', h2', h3', _⟩ => by rw [hr10] at h0'; cases h0'; rw [hr21] at h2'; cases h2'; rw [hr30] at h3'; cases h3'), sv_fail F E32 s32 t32 (fun x hx => (fR32 x hx).trans (fM x hx).symm) V32 hret g32_2 g32_18 hO g32_3 g32_4⟩
  · rw [hr30] at R30
    obtain ⟨a0_30, a1_30⟩ := R30
    have g30_10 : reg n30 a0 = BitVec.ofNat 32 0x0 := a0_30
    have g30_11 : reg n30 a1 = BitVec.ofNat 32 0x0 := by rw [a1_30]; rfl
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := keep_kk29.trans K30
    clear keep_kk29
    have w30_2d0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K30.w32 (by decide) (by decide)).trans w29_2d0
    have w30_2d4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K30.w32 (by decide) (by decide)).trans w29_2d4
    have w30_2d8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K30.w32 (by decide) (by decide)).trans w29_2d8
    have w30_2dc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K30.w32 (by decide) (by decide)).trans w29_2dc
    have w30_2e0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := (K30.w32 (by decide) (by decide)).trans w29_2e0
    have w30_2e4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := (K30.w32 (by decide) (by decide)).trans w29_2e4
    have w30_2e8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K30.w32 (by decide) (by decide)).trans w29_2e8
    have w30_2ec : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K30.w32 (by decide) (by decide)).trans w29_2ec
    have w30_2f0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K30.w32 (by decide) (by decide)).trans w29_2f0
    have w30_2f4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := (K30.w32 (by decide) (by decide)).trans w29_2f4
    have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K30.w32 (by decide) (by decide)).trans w29_420
    have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := (K30.w32 (by decide) (by decide)).trans w29_424
    have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K30.w32 (by decide) (by decide)).trans w29_428
    have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := (K30.w32 (by decide) (by decide)).trans w29_42c
    have b30_424 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_424
    have b30_425 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K30.b8 (by decide) (by decide)).trans b29_425
    have b30_426 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K30.b8 (by decide) (by decide)).trans b29_426
    have b30_427 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K30.b8 (by decide) (by decide)).trans b29_427
    clear b29_427 b29_426 b29_425 b29_424 w29_42c w29_428 w29_424 w29_420 w29_2fc w29_2f8 w29_2f4 w29_2f0 w29_2ec w29_2e8 w29_2e4 w29_2e0 w29_2dc w29_2d8 w29_2d4 w29_2d0 g29_11 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29 w28_2f4
    -- 0xAEC
    obtain ⟨n31, c31, u31⟩ := s30.block svTr1aec E30.self svTr1aec_end
      ⟨trivial, trivial, trivial⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have s31 : St n31.mem SV n31 0xAF0 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have rb31 : ∀ q, reg n31 q = (runBlock svTr1aec (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans c31
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by
      rw [rb31, runBlock_reg _ _ _ sp s30.zero (by decide), g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb31, runBlock_reg _ _ _ (3 : Fin 32) s30.zero (by decide), g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb31, runBlock_reg _ _ _ (4 : Fin 32) s30.zero (by decide), g30_4]
    have g31_9 : reg n31 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by
      rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
    have g31_11 : reg n31 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb31, runBlock_reg _ _ _ a1 s30.zero (by decide), g30_11]
    have g31_18 : reg n31 (18 : Fin 32) = out := by
      rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by
      rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = x20 := by
      rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = x21 := by
      rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = x22 := by
      rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = x23 := by
      rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = x24 := by
      rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = x25 := by
      rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = x26 := by
      rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = x27 := by
      rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
    have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb31]; simp +decide only [runBlock, BInstr.run, svTr1aec, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_11, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g31_10 : reg n31 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb31]; simp +decide only [runBlock, BInstr.run, svTr1aec, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_11, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_2d0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m31]; exact w30_2d0
    have w31_2d4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m31]; exact w30_2d4
    have w31_2d8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m31]; exact w30_2d8
    have w31_2dc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m31]; exact w30_2dc
    have w31_2e0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m31]; exact w30_2e0
    have w31_2e4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m31]; exact w30_2e4
    have w31_2e8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m31]; exact w30_2e8
    have w31_2ec : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m31]; exact w30_2ec
    have w31_2f0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_2f0
    have w31_2f4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_2f4
    have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_420
    have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_424
    have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_428
    have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_42c
    have b31_424 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m31]; exact b30_424
    have b31_425 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m31]; exact b30_425
    have b31_426 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m31]; exact b30_426
    have b31_427 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m31]; exact b30_427
    clear b30_427 b30_426 b30_425 b30_424 w30_42c w30_428 w30_424 w30_420 w30_2f4 w30_2f0 w30_2ec w30_2e8 w30_2e4 w30_2e0 w30_2dc w30_2d8 w30_2d4 w30_2d0 g30_11 g30_10 a1_30 a0_30
    -- 0xAF0: branch, not taken
    obtain ⟨n32, d32, u32⟩ := s31.notTaken E31.self 0xAF4 sv_at_af0
      (by decide) (by rw [g31_10, s31.zero]; decide)
    have s32 : St n32.mem SV n32 0xAF4 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
    have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u32.regs, g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = BitVec.ofNat 32 0x0 := by rw [u32.regs, g31_10]
    have g32_11 : reg n32 a1 = BitVec.ofNat 32 0x0 := by rw [u32.regs, g31_11]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = x24 := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = x25 := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = x27 := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_2d0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m32]; exact w31_2d0
    have w32_2d4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m32]; exact w31_2d4
    have w32_2d8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m32]; exact w31_2d8
    have w32_2dc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m32]; exact w31_2dc
    have w32_2e0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m32]; exact w31_2e0
    have w32_2e4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m32]; exact w31_2e4
    have w32_2e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m32]; exact w31_2e8
    have w32_2ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m32]; exact w31_2ec
    have w32_2f0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_2f0
    have w32_2f4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_2f4
    have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_420
    have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_424
    have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_428
    have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_42c
    have b32_424 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m32]; exact b31_424
    have b32_425 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m32]; exact b31_425
    have b32_426 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m32]; exact b31_426
    have b32_427 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m32]; exact b31_427
    clear b31_427 b31_426 b31_425 b31_424 w31_42c w31_428 w31_424 w31_420 w31_2f4 w31_2f0 w31_2ec w31_2e8 w31_2e4 w31_2e0 w31_2dc w31_2d8 w31_2d4 w31_2d0 g31_10 g31_8 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_11 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
    -- 0xAF4
    obtain ⟨n33, c33, u33⟩ := s32.block svTr1af4 E32.self svTr1af4_end
      ⟨trivial, trivial, trivial⟩
    have m33 : n33.mem = n32.mem := u33.mem
    have s33 : St n33.mem SV n33 0xAFA (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
    have rb33 : ∀ q, reg n33 q = (runBlock svTr1af4 (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
    have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
    have t33 : Steps n0 n33 := t32.trans c33
    have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
    have E33 : SvCode n33.mem := E32.fr F fr33
    have V33 : SvSaves B n33.mem v := V32.same m33
    have g33_2 : reg n33 sp = B + 0x21A0 := by
      rw [rb33, runBlock_reg _ _ _ sp s32.zero (by decide), g32_2]
    have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb33, runBlock_reg _ _ _ (3 : Fin 32) s32.zero (by decide), g32_3]
    have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb33, runBlock_reg _ _ _ (4 : Fin 32) s32.zero (by decide), g32_4]
    have g33_9 : reg n33 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by
      rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
    have g33_11 : reg n33 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb33, runBlock_reg _ _ _ a1 s32.zero (by decide), g32_11]
    have g33_18 : reg n33 (18 : Fin 32) = out := by
      rw [rb33, runBlock_reg _ _ _ (18 : Fin 32) s32.zero (by decide), g32_18]
    have g33_19 : reg n33 (19 : Fin 32) = bp := by
      rw [rb33, runBlock_reg _ _ _ (19 : Fin 32) s32.zero (by decide), g32_19]
    have g33_20 : reg n33 (20 : Fin 32) = x20 := by
      rw [rb33, runBlock_reg _ _ _ (20 : Fin 32) s32.zero (by decide), g32_20]
    have g33_21 : reg n33 (21 : Fin 32) = x21 := by
      rw [rb33, runBlock_reg _ _ _ (21 : Fin 32) s32.zero (by decide), g32_21]
    have g33_22 : reg n33 (22 : Fin 32) = x22 := by
      rw [rb33, runBlock_reg _ _ _ (22 : Fin 32) s32.zero (by decide), g32_22]
    have g33_23 : reg n33 (23 : Fin 32) = x23 := by
      rw [rb33, runBlock_reg _ _ _ (23 : Fin 32) s32.zero (by decide), g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = x24 := by
      rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = x25 := by
      rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = x26 := by
      rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = x27 := by
      rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
    have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb33]; simp +decide only [runBlock, BInstr.run, svTr1af4, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_10, g32_11, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb33]; simp +decide only [runBlock, BInstr.run, svTr1af4, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_10, g32_11, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m33]; exact keep_kk32
    clear keep_kk32
    have w33_2d0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m33]; exact w32_2d0
    have w33_2d4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m33]; exact w32_2d4
    have w33_2d8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m33]; exact w32_2d8
    have w33_2dc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m33]; exact w32_2dc
    have w33_2e0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m33]; exact w32_2e0
    have w33_2e4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m33]; exact w32_2e4
    have w33_2e8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m33]; exact w32_2e8
    have w33_2ec : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m33]; exact w32_2ec
    have w33_2f0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m33]; exact w32_2f0
    have w33_2f4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m33]; exact w32_2f4
    have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m33]; exact w32_420
    have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m33]; exact w32_424
    have w33_428 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m33]; exact w32_428
    have w33_42c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m33]; exact w32_42c
    have b33_424 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m33]; exact b32_424
    have b33_425 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m33]; exact b32_425
    have b33_426 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m33]; exact b32_426
    have b33_427 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m33]; exact b32_427
    clear b32_427 b32_426 b32_425 b32_424 w32_42c w32_428 w32_424 w32_420 w32_2f4 w32_2f0 w32_2ec w32_2e8 w32_2e4 w32_2e0 w32_2dc w32_2d8 w32_2d4 w32_2d0 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
    -- 0xAFA: branch, taken
    obtain ⟨n34, d34, u34⟩ := s33.taken E33.self 0x7A4 sv_at_afa
      (by decide) (by rw [g33_10, s33.zero]; decide)
    have s34 : St n34.mem SV n34 0x7A4 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
    have m34 : n34.mem = n33.mem := u34.mem
    have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
    have t34 : Steps n0 n34 := t33.trans (.single d34)
    have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.same m34
    have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, g33_4]
    have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u34.regs, g33_8]
    have g34_9 : reg n34 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [u34.regs, g33_9]
    have g34_10 : reg n34 a0 = BitVec.ofNat 32 0x0 := by rw [u34.regs, g33_10]
    have g34_11 : reg n34 a1 = BitVec.ofNat 32 0x0 := by rw [u34.regs, g33_11]
    have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, g33_18]
    have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, g33_19]
    have g34_20 : reg n34 (20 : Fin 32) = x20 := by rw [u34.regs, g33_20]
    have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [u34.regs, g33_21]
    have g34_22 : reg n34 (22 : Fin 32) = x22 := by rw [u34.regs, g33_22]
    have g34_23 : reg n34 (23 : Fin 32) = x23 := by rw [u34.regs, g33_23]
    have g34_24 : reg n34 (24 : Fin 32) = x24 := by rw [u34.regs, g33_24]
    have g34_25 : reg n34 (25 : Fin 32) = x25 := by rw [u34.regs, g33_25]
    have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [u34.regs, g33_26]
    have g34_27 : reg n34 (27 : Fin 32) = x27 := by rw [u34.regs, g33_27]
    have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m34]; exact keep_kk33
    clear keep_kk33
    have w34_2d0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m34]; exact w33_2d0
    have w34_2d4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m34]; exact w33_2d4
    have w34_2d8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m34]; exact w33_2d8
    have w34_2dc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m34]; exact w33_2dc
    have w34_2e0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m34]; exact w33_2e0
    have w34_2e4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m34]; exact w33_2e4
    have w34_2e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m34]; exact w33_2e8
    have w34_2ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m34]; exact w33_2ec
    have w34_2f0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m34]; exact w33_2f0
    have w34_2f4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m34]; exact w33_2f4
    have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m34]; exact w33_420
    have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m34]; exact w33_424
    have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m34]; exact w33_428
    have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m34]; exact w33_42c
    have b34_424 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m34]; exact b33_424
    have b34_425 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m34]; exact b33_425
    have b34_426 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m34]; exact b33_426
    have b34_427 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m34]; exact b33_427
    clear b33_427 b33_426 b33_425 b33_424 w33_42c w33_428 w33_424 w33_420 w33_2f4 w33_2f0 w33_2ec w33_2e8 w33_2e4 w33_2e0 w33_2dc w33_2d8 w33_2d4 w33_2d0 g33_10 g33_8 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_11 g33_9 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
    exact .inl ⟨(fun ⟨tl10', h0', h1', tl21', h2', h3', _⟩ => by rw [hr10] at h0'; cases h0'; rw [hr21] at h2'; cases h2'; rw [hr30] at h3'; cases h3'), sv_fail F E34 s34 t34 (fun x hx => (fR34 x hx).trans (fM x hx).symm) V34 hret g34_2 g34_18 hO g34_3 g34_4⟩
  obtain ⟨te30, hte30⟩ := ii_ok_elem hr30
  obtain ⟨d8_30, d12_30⟩ := A30 te30 hte30
  rw [hr30] at R30
  obtain ⟨a0_30, a1_30⟩ := R30
  have g30_10 : reg n30 a0 = BitVec.ofNat 32 0x0 := a0_30
  have g30_11 : reg n30 a1 = BitVec.ofNat 32 0x1 := by rw [a1_30]; rfl
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := keep_kk29.trans K30
  clear keep_kk29
  have w30_2d0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := (K30.w32 (by decide) (by decide)).trans w29_2d0
  have w30_2d4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := (K30.w32 (by decide) (by decide)).trans w29_2d4
  have w30_2d8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K30.w32 (by decide) (by decide)).trans w29_2d8
  have w30_2dc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K30.w32 (by decide) (by decide)).trans w29_2dc
  have w30_2e0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := (K30.w32 (by decide) (by decide)).trans w29_2e0
  have w30_2e4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := (K30.w32 (by decide) (by decide)).trans w29_2e4
  have w30_2e8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K30.w32 (by decide) (by decide)).trans w29_2e8
  have w30_2ec : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K30.w32 (by decide) (by decide)).trans w29_2ec
  have w30_2f0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K30.w32 (by decide) (by decide)).trans w29_2f0
  have w30_2f4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := (K30.w32 (by decide) (by decide)).trans w29_2f4
  have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K30.w32 (by decide) (by decide)).trans w29_420
  have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := (K30.w32 (by decide) (by decide)).trans w29_424
  have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := (K30.w32 (by decide) (by decide)).trans w29_428
  have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := (K30.w32 (by decide) (by decide)).trans w29_42c
  have b30_424 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_424
  have b30_425 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K30.b8 (by decide) (by decide)).trans b29_425
  have b30_426 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K30.b8 (by decide) (by decide)).trans b29_426
  have b30_427 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K30.b8 (by decide) (by decide)).trans b29_427
  have w30_2f8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (te30.header + te30.len) := d8_30
  have w30_2fc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) := d12_30
  clear b29_427 b29_426 b29_425 b29_424 w29_42c w29_428 w29_424 w29_420 w29_2fc w29_2f8 w29_2f4 w29_2f0 w29_2ec w29_2e8 w29_2e4 w29_2e0 w29_2dc w29_2d8 w29_2d4 w29_2d0 g29_11 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29 w28_2f4
  -- 0xAEC
  obtain ⟨n31, c31, u31⟩ := s30.block svTr1aec E30.self svTr1aec_end
    ⟨trivial, trivial, trivial⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have s31 : St n31.mem SV n31 0xAF0 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have rb31 : ∀ q, reg n31 q = (runBlock svTr1aec (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans c31
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by
    rw [rb31, runBlock_reg _ _ _ sp s30.zero (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (3 : Fin 32) s30.zero (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (4 : Fin 32) s30.zero (by decide), g30_4]
  have g31_9 : reg n31 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by
    rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
  have g31_11 : reg n31 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb31, runBlock_reg _ _ _ a1 s30.zero (by decide), g30_11]
  have g31_18 : reg n31 (18 : Fin 32) = out := by
    rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by
    rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = x20 := by
    rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by
    rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by
    rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = x23 := by
    rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = x24 := by
    rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = x25 := by
    rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by
    rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = x27 := by
    rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
  have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svTr1aec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_11, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g31_10 : reg n31 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svTr1aec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_11, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_2d0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m31]; exact w30_2d0
  have w31_2d4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m31]; exact w30_2d4
  have w31_2d8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m31]; exact w30_2d8
  have w31_2dc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m31]; exact w30_2dc
  have w31_2e0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m31]; exact w30_2e0
  have w31_2e4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m31]; exact w30_2e4
  have w31_2e8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m31]; exact w30_2e8
  have w31_2ec : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m31]; exact w30_2ec
  have w31_2f0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_2f0
  have w31_2f4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_2f4
  have w31_2f8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (te30.header + te30.len) := by rw [m31]; exact w30_2f8
  have w31_2fc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) := by rw [m31]; exact w30_2fc
  have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_420
  have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_424
  have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_428
  have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_42c
  have b31_424 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m31]; exact b30_424
  have b31_425 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m31]; exact b30_425
  have b31_426 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m31]; exact b30_426
  have b31_427 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m31]; exact b30_427
  clear w30_2fc w30_2f8 b30_427 b30_426 b30_425 b30_424 w30_42c w30_428 w30_424 w30_420 w30_2f4 w30_2f0 w30_2ec w30_2e8 w30_2e4 w30_2e0 w30_2dc w30_2d8 w30_2d4 w30_2d0 g30_11 g30_10 a1_30 a0_30 d12_30 d8_30 g30_2 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 V30 E30 fR30 t30 fr30 A30 K30 rk30 sp30 s30 c30
  -- 0xAF0: branch, not taken
  obtain ⟨n32, d32, u32⟩ := s31.notTaken E31.self 0xAF4 sv_at_af0
    (by decide) (by rw [g31_10, s31.zero]; decide)
  have s32 : St n32.mem SV n32 0xAF4 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [u32.regs, g31_9]
  have g32_10 : reg n32 a0 = BitVec.ofNat 32 0x0 := by rw [u32.regs, g31_10]
  have g32_11 : reg n32 a1 = BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_11]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [u32.regs, g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = x24 := by rw [u32.regs, g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = x25 := by rw [u32.regs, g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = x27 := by rw [u32.regs, g31_27]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_2d0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m32]; exact w31_2d0
  have w32_2d4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m32]; exact w31_2d4
  have w32_2d8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m32]; exact w31_2d8
  have w32_2dc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m32]; exact w31_2dc
  have w32_2e0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m32]; exact w31_2e0
  have w32_2e4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m32]; exact w31_2e4
  have w32_2e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m32]; exact w31_2e8
  have w32_2ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m32]; exact w31_2ec
  have w32_2f0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_2f0
  have w32_2f4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_2f4
  have w32_2f8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (te30.header + te30.len) := by rw [m32]; exact w31_2f8
  have w32_2fc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) := by rw [m32]; exact w31_2fc
  have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_420
  have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_424
  have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_428
  have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_42c
  have b32_424 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m32]; exact b31_424
  have b32_425 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m32]; exact b31_425
  have b32_426 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m32]; exact b31_426
  have b32_427 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m32]; exact b31_427
  clear b31_427 b31_426 b31_425 b31_424 w31_42c w31_428 w31_424 w31_420 w31_2fc w31_2f8 w31_2f4 w31_2f0 w31_2ec w31_2e8 w31_2e4 w31_2e0 w31_2dc w31_2d8 w31_2d4 w31_2d0 g31_10 g31_8 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_11 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
  -- 0xAF4
  obtain ⟨n33, c33, u33⟩ := s32.block svTr1af4 E32.self svTr1af4_end
    ⟨trivial, trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem SV n33 0xAFA (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock svTr1af4 (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans c33
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by
    rw [rb33, runBlock_reg _ _ _ sp s32.zero (by decide), g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb33, runBlock_reg _ _ _ (3 : Fin 32) s32.zero (by decide), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb33, runBlock_reg _ _ _ (4 : Fin 32) s32.zero (by decide), g32_4]
  have g33_9 : reg n33 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by
    rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
  have g33_11 : reg n33 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb33, runBlock_reg _ _ _ a1 s32.zero (by decide), g32_11]
  have g33_18 : reg n33 (18 : Fin 32) = out := by
    rw [rb33, runBlock_reg _ _ _ (18 : Fin 32) s32.zero (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by
    rw [rb33, runBlock_reg _ _ _ (19 : Fin 32) s32.zero (by decide), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = x20 := by
    rw [rb33, runBlock_reg _ _ _ (20 : Fin 32) s32.zero (by decide), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = x21 := by
    rw [rb33, runBlock_reg _ _ _ (21 : Fin 32) s32.zero (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = x22 := by
    rw [rb33, runBlock_reg _ _ _ (22 : Fin 32) s32.zero (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = x23 := by
    rw [rb33, runBlock_reg _ _ _ (23 : Fin 32) s32.zero (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = x24 := by
    rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = x25 := by
    rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by
    rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = x27 := by
    rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
  have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svTr1af4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_10, g32_11, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svTr1af4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_10, g32_11, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_2d0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m33]; exact w32_2d0
  have w33_2d4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m33]; exact w32_2d4
  have w33_2d8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m33]; exact w32_2d8
  have w33_2dc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m33]; exact w32_2dc
  have w33_2e0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m33]; exact w32_2e0
  have w33_2e4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m33]; exact w32_2e4
  have w33_2e8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m33]; exact w32_2e8
  have w33_2ec : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m33]; exact w32_2ec
  have w33_2f0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m33]; exact w32_2f0
  have w33_2f4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m33]; exact w32_2f4
  have w33_2f8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (te30.header + te30.len) := by rw [m33]; exact w32_2f8
  have w33_2fc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) := by rw [m33]; exact w32_2fc
  have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m33]; exact w32_420
  have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m33]; exact w32_424
  have w33_428 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m33]; exact w32_428
  have w33_42c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m33]; exact w32_42c
  have b33_424 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m33]; exact b32_424
  have b33_425 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m33]; exact b32_425
  have b33_426 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m33]; exact b32_426
  have b33_427 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m33]; exact b32_427
  clear b32_427 b32_426 b32_425 b32_424 w32_42c w32_428 w32_424 w32_420 w32_2fc w32_2f8 w32_2f4 w32_2f0 w32_2ec w32_2e8 w32_2e4 w32_2e0 w32_2dc w32_2d8 w32_2d4 w32_2d0 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0xAFA: branch, not taken
  obtain ⟨n34, d34, u34⟩ := s33.notTaken E33.self 0xAFE sv_at_afa
    (by decide) (by rw [g33_10, s33.zero]; decide)
  have s34 : St n34.mem SV n34 0xAFE (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans (.single d34)
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u34.regs, g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [u34.regs, g33_9]
  have g34_10 : reg n34 a0 = BitVec.ofNat 32 0x1 := by rw [u34.regs, g33_10]
  have g34_11 : reg n34 a1 = BitVec.ofNat 32 0x1 := by rw [u34.regs, g33_11]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = x20 := by rw [u34.regs, g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [u34.regs, g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = x22 := by rw [u34.regs, g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = x23 := by rw [u34.regs, g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = x24 := by rw [u34.regs, g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = x25 := by rw [u34.regs, g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [u34.regs, g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = x27 := by rw [u34.regs, g33_27]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_2d0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m34]; exact w33_2d0
  have w34_2d4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m34]; exact w33_2d4
  have w34_2d8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m34]; exact w33_2d8
  have w34_2dc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m34]; exact w33_2dc
  have w34_2e0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m34]; exact w33_2e0
  have w34_2e4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m34]; exact w33_2e4
  have w34_2e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m34]; exact w33_2e8
  have w34_2ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m34]; exact w33_2ec
  have w34_2f0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m34]; exact w33_2f0
  have w34_2f4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m34]; exact w33_2f4
  have w34_2f8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (te30.header + te30.len) := by rw [m34]; exact w33_2f8
  have w34_2fc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) := by rw [m34]; exact w33_2fc
  have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m34]; exact w33_420
  have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m34]; exact w33_424
  have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m34]; exact w33_428
  have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m34]; exact w33_42c
  have b34_424 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m34]; exact b33_424
  have b34_425 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m34]; exact b33_425
  have b34_426 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m34]; exact b33_426
  have b34_427 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m34]; exact b33_427
  clear b33_427 b33_426 b33_425 b33_424 w33_42c w33_428 w33_424 w33_420 w33_2fc w33_2f8 w33_2f4 w33_2f0 w33_2ec w33_2e8 w33_2e4 w33_2e0 w33_2dc w33_2d8 w33_2d4 w33_2d0 g33_10 g33_8 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_11 g33_9 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
  -- 0xAFE: lw
  obtain ⟨n35, d35, u35⟩ := s34.lw E34.self sv_at_afe (off' := 0xB02) (by decide)
    (by rw [g34_2, show B + 0x21A0 + 0x2FC = B + 0x21A0 + BitVec.ofNat 32 0x2FC by sv_addr]; exact sv_al F (by decide) (by decide))
  have s35 : St n35.mem SV n35 0xB02 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans (.single d35)
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [u35.regs, upd_ne (by decide) (by decide), g34_9]
  have g35_11 : reg n35 a1 = BitVec.ofNat 32 0x1 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_11]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, upd_ne (by decide) (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, upd_ne (by decide) (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = x20 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = x23 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = x24 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = x25 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = x27 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_27]
  have g35_10 : reg n35 a0 = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) := by
    rw [u35.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g34_2, show B + 0x21A0 + 0x2FC = B + 0x21A0 + BitVec.ofNat 32 0x2FC by sv_addr, w34_2fc]
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_2d0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m35]; exact w34_2d0
  have w35_2d4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m35]; exact w34_2d4
  have w35_2d8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m35]; exact w34_2d8
  have w35_2dc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m35]; exact w34_2dc
  have w35_2e0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m35]; exact w34_2e0
  have w35_2e4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m35]; exact w34_2e4
  have w35_2e8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m35]; exact w34_2e8
  have w35_2ec : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m35]; exact w34_2ec
  have w35_2f0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m35]; exact w34_2f0
  have w35_2f4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m35]; exact w34_2f4
  have w35_2f8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (te30.header + te30.len) := by rw [m35]; exact w34_2f8
  have w35_2fc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) := by rw [m35]; exact w34_2fc
  have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m35]; exact w34_420
  have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m35]; exact w34_424
  have w35_428 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m35]; exact w34_428
  have w35_42c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m35]; exact w34_42c
  have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m35]; exact b34_424
  have b35_425 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m35]; exact b34_425
  have b35_426 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m35]; exact b34_426
  have b35_427 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m35]; exact b34_427
  clear b34_427 b34_426 b34_425 b34_424 w34_42c w34_428 w34_424 w34_420 w34_2fc w34_2f8 w34_2f4 w34_2f0 w34_2ec w34_2e8 w34_2e4 w34_2e0 w34_2dc w34_2d8 w34_2d4 w34_2d0 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_11 g34_10 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
  by_cases hsrem : (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) = 0
  rotate_left
  · -- 0xB02: branch, taken
    obtain ⟨n36, d36, u36⟩ := s35.taken E35.self 0x7A4 sv_at_b02
      (by decide) (by rw [g35_10, s35.zero]; exact br_bne_t hsrem)
    have s36 : St n36.mem SV n36 0x7A4 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
    have m36 : n36.mem = n35.mem := u36.mem
    have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
    have t36 : Steps n0 n36 := t35.trans (.single d36)
    have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
    have E36 : SvCode n36.mem := E35.fr F fr36
    have V36 : SvSaves B n36.mem v := V35.same m36
    have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, g35_2]
    have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, g35_3]
    have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, g35_4]
    have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u36.regs, g35_8]
    have g36_9 : reg n36 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [u36.regs, g35_9]
    have g36_10 : reg n36 a0 = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) := by rw [u36.regs, g35_10]
    have g36_11 : reg n36 a1 = BitVec.ofNat 32 0x1 := by rw [u36.regs, g35_11]
    have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, g35_18]
    have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, g35_19]
    have g36_20 : reg n36 (20 : Fin 32) = x20 := by rw [u36.regs, g35_20]
    have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, g35_21]
    have g36_22 : reg n36 (22 : Fin 32) = x22 := by rw [u36.regs, g35_22]
    have g36_23 : reg n36 (23 : Fin 32) = x23 := by rw [u36.regs, g35_23]
    have g36_24 : reg n36 (24 : Fin 32) = x24 := by rw [u36.regs, g35_24]
    have g36_25 : reg n36 (25 : Fin 32) = x25 := by rw [u36.regs, g35_25]
    have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, g35_26]
    have g36_27 : reg n36 (27 : Fin 32) = x27 := by rw [u36.regs, g35_27]
    have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m36]; exact keep_kk35
    clear keep_kk35
    have w36_2d0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m36]; exact w35_2d0
    have w36_2d4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m36]; exact w35_2d4
    have w36_2d8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m36]; exact w35_2d8
    have w36_2dc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m36]; exact w35_2dc
    have w36_2e0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m36]; exact w35_2e0
    have w36_2e4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m36]; exact w35_2e4
    have w36_2e8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m36]; exact w35_2e8
    have w36_2ec : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m36]; exact w35_2ec
    have w36_2f0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m36]; exact w35_2f0
    have w36_2f4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m36]; exact w35_2f4
    have w36_2f8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (te30.header + te30.len) := by rw [m36]; exact w35_2f8
    have w36_2fc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) := by rw [m36]; exact w35_2fc
    have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m36]; exact w35_420
    have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m36]; exact w35_424
    have w36_428 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m36]; exact w35_428
    have w36_42c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m36]; exact w35_42c
    have b36_424 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m36]; exact b35_424
    have b36_425 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m36]; exact b35_425
    have b36_426 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m36]; exact b35_426
    have b36_427 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m36]; exact b35_427
    clear b35_427 b35_426 b35_425 b35_424 w35_42c w35_428 w35_424 w35_420 w35_2fc w35_2f8 w35_2f4 w35_2f0 w35_2ec w35_2e8 w35_2e4 w35_2e0 w35_2dc w35_2d8 w35_2d4 w35_2d0 g35_10 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_11 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
    exact .inl ⟨(fun ⟨tl10', h0', h1', tl21', h2', h3', te30', h4', h5', _⟩ => by rw [hr10] at h0'; cases h0'; rw [hr21] at h2'; cases h2'; rw [hr30] at h3'; cases h3'; rw [hte30] at h4'; cases h4'; exact hsrem h5'), sv_fail F E36 s36 t36 (fun x hx => (fR36 x hx).trans (fM x hx).symm) V36 hret g36_2 g36_18 hO g36_3 g36_4⟩
  -- 0xB02: branch, not taken
  obtain ⟨n36, d36, u36⟩ := s35.notTaken E35.self 0xB06 sv_at_b02
    (by decide) (by rw [g35_10, s35.zero]; exact br_bne_f hsrem)
  have s36 : St n36.mem SV n36 0xB06 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u36.regs, g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [u36.regs, g35_9]
  have g36_10 : reg n36 a0 = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) := by rw [u36.regs, g35_10]
  have g36_11 : reg n36 a1 = BitVec.ofNat 32 0x1 := by rw [u36.regs, g35_11]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = x20 := by rw [u36.regs, g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = x22 := by rw [u36.regs, g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = x23 := by rw [u36.regs, g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = x24 := by rw [u36.regs, g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = x25 := by rw [u36.regs, g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = x27 := by rw [u36.regs, g35_27]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_2d0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D0) = tsp := by rw [m36]; exact w35_2d0
  have w36_2d4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D4) = tsl := by rw [m36]; exact w35_2d4
  have w36_2d8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2D8) = (tsp) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m36]; exact w35_2d8
  have w36_2dc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2DC) = (tsl) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m36]; exact w35_2dc
  have w36_2e0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (tsp) + BitVec.ofNat 32 tl10.header := by rw [m36]; exact w35_2e0
  have w36_2e4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl10.len := by rw [m36]; exact w35_2e4
  have w36_2e8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m36]; exact w35_2e8
  have w36_2ec : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m36]; exact w35_2ec
  have w36_2f0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F0) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m36]; exact w35_2f0
  have w36_2f4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F4) = BitVec.ofNat 32 tl21.len := by rw [m36]; exact w35_2f4
  have w36_2f8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2F8) = (((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (te30.header + te30.len) := by rw [m36]; exact w35_2f8
  have w36_2fc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2FC) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (te30.header + te30.len) := by rw [m36]; exact w35_2fc
  have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m36]; exact w35_420
  have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m36]; exact w35_424
  have w36_428 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((tsp) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 tl21.header := by rw [m36]; exact w35_428
  have w36_42c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m36]; exact w35_42c
  have b36_424 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m36]; exact b35_424
  have b36_425 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m36]; exact b35_425
  have b36_426 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m36]; exact b35_426
  have b36_427 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m36]; exact b35_427
  clear b35_427 b35_426 b35_425 b35_424 w35_42c w35_428 w35_424 w35_420 w35_2fc w35_2f8 w35_2f4 w35_2f0 w35_2ec w35_2e8 w35_2e4 w35_2e0 w35_2dc w35_2d8 w35_2d4 w35_2d0 g35_10 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_11 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
  exact .inr ⟨tl10, hr10, hrem, tl21, hr21, hr30, te30, hte30, hsrem, n36, t36, s36, E36, V36, fR36, g36_2, g36_3, g36_4, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, w36_2e8, w36_2ec, keep_kk36.mono (by decide)⟩

end C3.RV32.Sv
