import C3BootProofs.Proofs.SvRk

/-!
# `sigstore::verify`: the entry's index against the checkpoint's size

From 0x17F8 to 0x189A: the checkpoint's key id, log id, size, and root go to offset 0x380, and the entry's 64-bit index is below the size.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCr1e17fa : List BInstr :=
  [.aluImm .add a1 a1 0x5, .aluImm .add a0 sp 0x27C, .aluImm .add a2 x0 0x13]
theorem svCr1e17fa_end : blockEnd sigstoreVerifyCode 0x17FA svCr1e17fa = some 0x1800 := by
  simp only [svCr1e17fa]
  rw [blockEnd, sv_at_17fa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_17fc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_17fe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCr1e1808 : List BInstr :=
  [.aluImm .add a0 sp 0x25C, .aluImm .add a1 sp 0x3E0, .aluImm .add a2 x0 0x1F]
theorem svCr1e1808_end : blockEnd sigstoreVerifyCode 0x1808 svCr1e1808 = some 0x180E := by
  simp only [svCr1e1808]
  rw [blockEnd, sv_at_1808]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_180a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_180c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCr1e181a : List BInstr :=
  [.aluImm .add a0 sp 0x385, .aluImm .add a1 sp 0x27C, .aluImm .add a2 x0 0x13]
theorem svCr1e181a_end : blockEnd sigstoreVerifyCode 0x181A svCr1e181a = some 0x1822 := by
  simp only [svCr1e181a]
  rw [blockEnd, sv_at_181a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_181e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1820]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCr1e183c : List BInstr :=
  [.aluImm .add a0 sp 0x3A9, .aluImm .add a1 sp 0x25C, .aluImm .add a2 x0 0x1F]
theorem svCr1e183c_end : blockEnd sigstoreVerifyCode 0x183C svCr1e183c = some 0x1844 := by
  simp only [svCr1e183c]
  rw [blockEnd, sv_at_183c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1840]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1842]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCr1e1856 : List BInstr :=
  [.aluImm .add a1 sp 0x380]
theorem svCr1e1856_end : blockEnd sigstoreVerifyCode 0x1856 svCr1e1856 = some 0x1858 := by
  simp only [svCr1e1856]
  rw [blockEnd, sv_at_1856]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCr1e1892 : List BInstr :=
  [.alu .sltu a0 (21 : Fin 32) a0]
theorem svCr1e1892_end : blockEnd sigstoreVerifyCode 0x1892 svCr1e1892 = some 0x1896 := by
  simp only [svCr1e1892]
  rw [blockEnd, sv_at_1892]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCr1e19a2 : List BInstr :=
  [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFB01]
theorem svCr1e19a2_end : blockEnd sigstoreVerifyCode 0x19A2 svCr1e19a2 = some 0x19A8 := by
  simp only [svCr1e19a2]
  rw [blockEnd, sv_at_19a2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_19a4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_cr1e {B out bp x20 x21 x22 x23 x24 x25 x26 x27 kp w1c w40 q w64 w74 lih lil : Word} {rt : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x17F8 (reg n0))
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
    (w0_1c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c)
    (w0_20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (q0_3e0 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))
    (RS : SvRoSep B)
    (lid_in : SvIn B (q + BitVec.ofNat 32 0x5) 19)
    (h40 : w40 ≠ 0)
    (hlih : memLoad32 M0 (bp + 0x2C) = lih)
    (hlil : memLoad32 M0 (bp + 0x28) = lil)
    (lih_in : SvIn B (bp + 0x2C) 4)
    (lil_in : SvIn B (bp + 0x28) 4)
    (a_lih : (bp + 0x2C).toNat % 4 = 0)
    (a_lil : (bp + 0x28).toNat % 4 = 0)
    (hhi : lih = w74) :
    (¬ ((aluEval .sltu (lil) (w64) ≠ 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((aluEval .sltu (lil) (w64) ≠ 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x189A (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = lil ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = lih ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        (∀ j, j < 19 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 19 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x17F8: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_17f8 (off' := 0x17FA) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0x17FA (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, upd_ne (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = x24 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = x27 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_11 : reg n1 a1 = q := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w0_4c]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_1c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m1]; exact w0_1c
  have w1_20 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m1]; exact w0_20
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m1]; exact w0_34
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m1]; exact w0_40
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m1]; exact w0_4c
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m1]; exact w0_64
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m1]; exact w0_74
  have q1_3e0 : ∀ j, j < 31 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m1]; exact q0_3e0 j hj
  -- 0x17FA
  obtain ⟨n2, c2, u2⟩ := s1.block svCr1e17fa E1.self svCr1e17fa_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem SV n2 0x1800 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock svCr1e17fa (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by
    rw [rb2, runBlock_reg _ _ _ sp s1.zero (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb2, runBlock_reg _ _ _ (3 : Fin 32) s1.zero (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb2, runBlock_reg _ _ _ (4 : Fin 32) s1.zero (by decide), g1_4]
  have g2_18 : reg n2 (18 : Fin 32) = out := by
    rw [rb2, runBlock_reg _ _ _ (18 : Fin 32) s1.zero (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by
    rw [rb2, runBlock_reg _ _ _ (19 : Fin 32) s1.zero (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by
    rw [rb2, runBlock_reg _ _ _ (20 : Fin 32) s1.zero (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by
    rw [rb2, runBlock_reg _ _ _ (21 : Fin 32) s1.zero (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by
    rw [rb2, runBlock_reg _ _ _ (22 : Fin 32) s1.zero (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by
    rw [rb2, runBlock_reg _ _ _ (23 : Fin 32) s1.zero (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by
    rw [rb2, runBlock_reg _ _ _ (24 : Fin 32) s1.zero (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by
    rw [rb2, runBlock_reg _ _ _ (25 : Fin 32) s1.zero (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by
    rw [rb2, runBlock_reg _ _ _ (26 : Fin 32) s1.zero (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = x27 := by
    rw [rb2, runBlock_reg _ _ _ (27 : Fin 32) s1.zero (by decide), g1_27]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x27C := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svCr1e17fa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_11, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g2_11 : reg n2 a1 = (q) + BitVec.ofNat 32 0x5 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svCr1e17fa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_11, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g2_12 : reg n2 a2 = BitVec.ofNat 32 0x13 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svCr1e17fa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_11, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_1c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m2]; exact w1_1c
  have w2_20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m2]; exact w1_20
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m2]; exact w1_34
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m2]; exact w1_40
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m2]; exact w1_4c
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m2]; exact w1_64
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m2]; exact w1_74
  have q2_3e0 : ∀ j, j < 31 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m2]; exact q1_3e0 j hj
  clear q1_3e0 w1_74 w1_64 w1_4c w1_40 w1_34 w1_20 w1_1c g1_11 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x1800: memcpy from the bundle
  obtain ⟨n3, P3, K3, X3⟩ := sv_mcRo2 (c := 0x27C) (N := 0x13) F RS E2 s2 sv_at_1800 sv_at_1804
    (by decide) (by decide) g2_2 g2_10 g2_11 g2_12 (by decide) (.inl lid_in)
  have s3 := P3.st
  have fr3 := P3.fr
  have t3 : Steps n0 n3 := t2.trans P3.steps
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.keep K3 (by decide)
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [P3.regs sp (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P3.regs (3 : Fin 32) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P3.regs (4 : Fin 32) (by decide), g2_4]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [P3.regs (18 : Fin 32) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [P3.regs (19 : Fin 32) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [P3.regs (20 : Fin 32) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [P3.regs (21 : Fin 32) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [P3.regs (22 : Fin 32) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [P3.regs (23 : Fin 32) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [P3.regs (24 : Fin 32) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [P3.regs (25 : Fin 32) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [P3.regs (26 : Fin 32) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [P3.regs (27 : Fin 32) (by decide), g2_27]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x27C, 0x13)] := keep_kk2.trans K3.toL
  clear keep_kk2
  have w3_1c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := (K3.w32 (by decide) (by decide)).trans w2_1c
  have w3_20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K3.w32 (by decide) (by decide)).trans w2_20
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K3.w32 (by decide) (by decide)).trans w2_34
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K3.w32 (by decide) (by decide)).trans w2_40
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K3.w32 (by decide) (by decide)).trans w2_4c
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K3.w32 (by decide) (by decide)).trans w2_64
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K3.w32 (by decide) (by decide)).trans w2_74
  have q3_3e0 : ∀ j, j < 31 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K3.range (by decide) (by decide) j hj).trans (q2_3e0 j hj)
  have q3_27c : ∀ j, j < 19 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) :=
    fun j hj => (X3 j hj).trans (fR2 _ (SvRo2.r RS (.inl lid_in) hj))
  clear q2_3e0 w2_74 w2_64 w2_4c w2_40 w2_34 w2_20 w2_1c g2_12 g2_11 g2_10 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0x1808
  obtain ⟨n4, c4, u4⟩ := s3.block svCr1e1808 E3.self svCr1e1808_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x180E (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svCr1e1808 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x25C := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svCr1e1808, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g4_11 : reg n4 a1 = B + 0x21A0 + BitVec.ofNat 32 0x3E0 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svCr1e1808, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g4_12 : reg n4 a2 = BitVec.ofNat 32 0x1F := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svCr1e1808, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x27C, 0x13)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_1c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m4]; exact w3_1c
  have w4_20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m4]; exact w3_20
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m4]; exact w3_34
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m4]; exact w3_40
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m4]; exact w3_4c
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m4]; exact w3_64
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m4]; exact w3_74
  have q4_27c : ∀ j, j < 19 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m4]; exact q3_27c j hj
  have q4_3e0 : ∀ j, j < 31 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m4]; exact q3_3e0 j hj
  clear q3_27c q3_3e0 w3_74 w3_64 w3_4c w3_40 w3_34 w3_20 w3_1c g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 s3 X3 K3 P3
  -- 0x180E: memcpy
  obtain ⟨n5, P5, K5, X5⟩ := sv_mc (c := 0x25C) (d := 0x3E0) (N := 0x1F) F E4 s4 sv_at_180e sv_at_1812
    (by decide) (by decide) g4_2 g4_10 g4_11 g4_12
    (by decide) (by decide) (by decide)
  have s5 := P5.st
  have fr5 := P5.fr
  have t5 : Steps n0 n5 := t4.trans P5.steps
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keep K5 (by decide)
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [P5.regs sp (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P5.regs (3 : Fin 32) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P5.regs (4 : Fin 32) (by decide), g4_4]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [P5.regs (18 : Fin 32) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [P5.regs (19 : Fin 32) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [P5.regs (20 : Fin 32) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [P5.regs (21 : Fin 32) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [P5.regs (22 : Fin 32) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [P5.regs (23 : Fin 32) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [P5.regs (24 : Fin 32) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [P5.regs (25 : Fin 32) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [P5.regs (26 : Fin 32) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [P5.regs (27 : Fin 32) (by decide), g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x27C, 0x13), (0x25C, 0x1F)] := keep_kk4.trans K5.toL
  clear keep_kk4
  have w5_1c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := (K5.w32 (by decide) (by decide)).trans w4_1c
  have w5_20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K5.w32 (by decide) (by decide)).trans w4_20
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K5.w32 (by decide) (by decide)).trans w4_34
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K5.w32 (by decide) (by decide)).trans w4_40
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K5.w32 (by decide) (by decide)).trans w4_4c
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K5.w32 (by decide) (by decide)).trans w4_64
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K5.w32 (by decide) (by decide)).trans w4_74
  have q5_27c : ∀ j, j < 19 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K5.range (by decide) (by decide) j hj).trans (q4_27c j hj)
  have q5_3e0 : ∀ j, j < 31 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K5.range (by decide) (by decide) j hj).trans (q4_3e0 j hj)
  have q5_25c : ∀ j, j < 31 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by
    rw [show 0x25C + j = 0x25C + (0x0 + j) by omega, X5 (0x0 + j) (by omega),
      show 0x3E0 + (0x0 + j) = 0x3E0 + j by omega]; exact q4_3e0 j (by omega)
  clear q4_3e0 q4_27c w4_74 w4_64 w4_4c w4_40 w4_34 w4_20 w4_1c g4_12 g4_11 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x1816: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_1816 (off' := 0x1818) (by decide)
    (by rw [g5_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0x1818 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_10 : reg n6 a0 = w40 := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr, w5_40]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x27C, 0x13), (0x25C, 0x1F)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_1c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m6]; exact w5_1c
  have w6_20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m6]; exact w5_20
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m6]; exact w5_34
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m6]; exact w5_40
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m6]; exact w5_4c
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m6]; exact w5_64
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m6]; exact w5_74
  have q6_25c : ∀ j, j < 31 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_25c j hj
  have q6_27c : ∀ j, j < 19 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_27c j hj
  have q6_3e0 : ∀ j, j < 31 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_3e0 j hj
  clear q5_25c q5_3e0 q5_27c w5_74 w5_64 w5_4c w5_40 w5_34 w5_20 w5_1c g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 s5 X5 K5 P5
  -- 0x1818: branch, not taken
  obtain ⟨n7, d7, u7⟩ := s6.notTaken E6.self 0x181A sv_at_1818
    (by decide) (by rw [g6_10, s6.zero]; exact br_beq_f h40)
  have s7 : St n7.mem SV n7 0x181A (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
  have g7_10 : reg n7 a0 = w40 := by rw [u7.regs, g6_10]
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
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x27C, 0x13), (0x25C, 0x1F)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_1c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m7]; exact w6_1c
  have w7_20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m7]; exact w6_20
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m7]; exact w6_34
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m7]; exact w6_40
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m7]; exact w6_4c
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m7]; exact w6_74
  have q7_25c : ∀ j, j < 31 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m7]; exact q6_25c j hj
  have q7_27c : ∀ j, j < 19 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_27c j hj
  have q7_3e0 : ∀ j, j < 31 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m7]; exact q6_3e0 j hj
  clear q6_3e0 q6_27c q6_25c w6_74 w6_64 w6_4c w6_40 w6_34 w6_20 w6_1c g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x181A
  obtain ⟨n8, c8, u8⟩ := s7.block svCr1e181a E7.self svCr1e181a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x1822 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svCr1e181a (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x385 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svCr1e181a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_11 : reg n8 a1 = B + 0x21A0 + BitVec.ofNat 32 0x27C := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svCr1e181a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_12 : reg n8 a2 = BitVec.ofNat 32 0x13 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svCr1e181a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x27C, 0x13), (0x25C, 0x1F)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_1c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m8]; exact w7_1c
  have w8_20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m8]; exact w7_20
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m8]; exact w7_34
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m8]; exact w7_40
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m8]; exact w7_4c
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
  have q8_25c : ∀ j, j < 31 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m8]; exact q7_25c j hj
  have q8_27c : ∀ j, j < 19 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m8]; exact q7_27c j hj
  have q8_3e0 : ∀ j, j < 31 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m8]; exact q7_3e0 j hj
  clear q7_3e0 q7_27c q7_25c w7_74 w7_64 w7_4c w7_40 w7_34 w7_20 w7_1c g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x1822: memcpy
  obtain ⟨n9, P9, K9, X9⟩ := sv_mc (c := 0x385) (d := 0x27C) (N := 0x13) F E8 s8 sv_at_1822 sv_at_1826
    (by decide) (by decide) g8_2 g8_10 g8_11 g8_12
    (by decide) (by decide) (by decide)
  have s9 := P9.st
  have fr9 := P9.fr
  have t9 : Steps n0 n9 := t8.trans P9.steps
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [P9.regs sp (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P9.regs (3 : Fin 32) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P9.regs (4 : Fin 32) (by decide), g8_4]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [P9.regs (18 : Fin 32) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [P9.regs (19 : Fin 32) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [P9.regs (20 : Fin 32) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [P9.regs (21 : Fin 32) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [P9.regs (22 : Fin 32) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [P9.regs (23 : Fin 32) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [P9.regs (24 : Fin 32) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [P9.regs (25 : Fin 32) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [P9.regs (26 : Fin 32) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [P9.regs (27 : Fin 32) (by decide), g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have w9_1c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := (K9.w32 (by decide) (by decide)).trans w8_1c
  have w9_20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K9.w32 (by decide) (by decide)).trans w8_20
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K9.w32 (by decide) (by decide)).trans w8_34
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K9.w32 (by decide) (by decide)).trans w8_40
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K9.w32 (by decide) (by decide)).trans w8_4c
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K9.w32 (by decide) (by decide)).trans w8_64
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K9.w32 (by decide) (by decide)).trans w8_74
  have q9_25c : ∀ j, j < 31 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_25c j hj)
  have q9_27c : ∀ j, j < 19 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_27c j hj)
  have q9_3e0 : ∀ j, j < 31 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_3e0 j hj)
  have q9_385 : ∀ j, j < 19 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x385 + j = 0x385 + (0x0 + j) by omega, X9 (0x0 + j) (by omega),
      show 0x27C + (0x0 + j) = 0x27C + j by omega]; exact q8_27c j (by omega)
  clear q8_3e0 q8_27c q8_25c w8_74 w8_64 w8_4c w8_40 w8_34 w8_20 w8_1c g8_12 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0x182A: lw
  obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_182a (off' := 0x182C) (by decide)
    (by rw [g9_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s10 : St n10.mem SV n10 0x182C (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
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
  have g10_10 : reg n10 a0 = kp := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr, w9_34]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_1c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m10]; exact w9_1c
  have w10_20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m10]; exact w9_20
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m10]; exact w9_34
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m10]; exact w9_40
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m10]; exact w9_4c
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
  have q10_25c : ∀ j, j < 31 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_25c j hj
  have q10_27c : ∀ j, j < 19 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m10]; exact q9_27c j hj
  have q10_385 : ∀ j, j < 19 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m10]; exact q9_385 j hj
  have q10_3e0 : ∀ j, j < 31 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_3e0 j hj
  clear q9_385 q9_3e0 q9_27c q9_25c w9_74 w9_64 w9_4c w9_40 w9_34 w9_20 w9_1c g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 s9 X9 K9 P9
  -- 0x182C: sw
  obtain ⟨n11, d11, s11, fr11, K11, W11, rg11⟩ := sv_sw F E10 s10 sv_at_182c (off' := 0x1830) (c := 0x398)
    (by decide) (by rw [g10_2]; sv_addr) (by decide) (by decide)
  have t11 : Steps n0 n11 := t10.trans d11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rg11 sp, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg11 (3 : Fin 32), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg11 (4 : Fin 32), g10_4]
  have g11_10 : reg n11 a0 = kp := by rw [rg11 a0, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rg11 (18 : Fin 32), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rg11 (19 : Fin 32), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [rg11 (20 : Fin 32), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [rg11 (21 : Fin 32), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [rg11 (22 : Fin 32), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [rg11 (23 : Fin 32), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [rg11 (24 : Fin 32), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [rg11 (25 : Fin 32), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [rg11 (26 : Fin 32), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [rg11 (27 : Fin 32), g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have w11_1c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := (K11.w32 (by decide) (by decide)).trans w10_1c
  have w11_20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K11.w32 (by decide) (by decide)).trans w10_20
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K11.w32 (by decide) (by decide)).trans w10_34
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K11.w32 (by decide) (by decide)).trans w10_40
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K11.w32 (by decide) (by decide)).trans w10_4c
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K11.w32 (by decide) (by decide)).trans w10_64
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K11.w32 (by decide) (by decide)).trans w10_74
  have w11_398 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [W11, g10_10]
  have q11_25c : ∀ j, j < 31 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_25c j hj)
  have q11_27c : ∀ j, j < 19 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_27c j hj)
  have q11_385 : ∀ j, j < 19 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_385 j hj)
  have q11_3e0 : ∀ j, j < 31 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_3e0 j hj)
  clear q10_3e0 q10_385 q10_27c q10_25c w10_74 w10_64 w10_4c w10_40 w10_34 w10_20 w10_1c g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x1830: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_1830 (off' := 0x1832) (by decide)
    (by rw [g11_2, show B + 0x21A0 + 0x1C = B + 0x21A0 + BitVec.ofNat 32 0x1C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x1832 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
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
  have g12_10 : reg n12 a0 = w1c := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x1C = B + 0x21A0 + BitVec.ofNat 32 0x1C by sv_addr, w11_1c]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_1c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m12]; exact w11_1c
  have w12_20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m12]; exact w11_20
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m12]; exact w11_34
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m12]; exact w11_40
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m12]; exact w11_4c
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m12]; exact w11_74
  have w12_398 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m12]; exact w11_398
  have q12_25c : ∀ j, j < 31 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m12]; exact q11_25c j hj
  have q12_27c : ∀ j, j < 19 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_27c j hj
  have q12_385 : ∀ j, j < 19 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_385 j hj
  have q12_3e0 : ∀ j, j < 31 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m12]; exact q11_3e0 j hj
  clear q11_3e0 q11_385 q11_27c q11_25c w11_398 w11_74 w11_64 w11_4c w11_40 w11_34 w11_20 w11_1c g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 rg11 W11 K11 fr11 s11 d11
  -- 0x1832: sw
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := sv_sw F E12 s12 sv_at_1832 (off' := 0x1836) (c := 0x39C)
    (by decide) (by rw [g12_2]; sv_addr) (by decide) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_10 : reg n13 a0 = w1c := by rw [rg13 a0, g12_10]
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
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_1c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := (K13.w32 (by decide) (by decide)).trans w12_1c
  have w13_20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K13.w32 (by decide) (by decide)).trans w12_20
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K13.w32 (by decide) (by decide)).trans w12_34
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K13.w32 (by decide) (by decide)).trans w12_40
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K13.w32 (by decide) (by decide)).trans w12_4c
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K13.w32 (by decide) (by decide)).trans w12_64
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K13.w32 (by decide) (by decide)).trans w12_74
  have w13_398 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := (K13.w32 (by decide) (by decide)).trans w12_398
  have w13_39c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [W13, g12_10]
  have q13_25c : ∀ j, j < 31 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K13.range (by decide) (by decide) j hj).trans (q12_25c j hj)
  have q13_27c : ∀ j, j < 19 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K13.range (by decide) (by decide) j hj).trans (q12_27c j hj)
  have q13_385 : ∀ j, j < 19 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K13.range (by decide) (by decide) j hj).trans (q12_385 j hj)
  have q13_3e0 : ∀ j, j < 31 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K13.range (by decide) (by decide) j hj).trans (q12_3e0 j hj)
  clear q12_3e0 q12_385 q12_27c q12_25c w12_398 w12_74 w12_64 w12_4c w12_40 w12_34 w12_20 w12_1c g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x1836: lw
  obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_1836 (off' := 0x1838) (by decide)
    (by rw [g13_2, show B + 0x21A0 + 0x20 = B + 0x21A0 + BitVec.ofNat 32 0x20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s14 : St n14.mem SV n14 0x1838 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
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
  have g14_10 : reg n14 a0 = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by
    rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g13_2, show B + 0x21A0 + 0x20 = B + 0x21A0 + BitVec.ofNat 32 0x20 by sv_addr, w13_20]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_1c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m14]; exact w13_1c
  have w14_20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m14]; exact w13_20
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m14]; exact w13_34
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m14]; exact w13_40
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m14]; exact w13_4c
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m14]; exact w13_64
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m14]; exact w13_74
  have w14_398 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m14]; exact w13_398
  have w14_39c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m14]; exact w13_39c
  have q14_25c : ∀ j, j < 31 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m14]; exact q13_25c j hj
  have q14_27c : ∀ j, j < 19 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m14]; exact q13_27c j hj
  have q14_385 : ∀ j, j < 19 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m14]; exact q13_385 j hj
  have q14_3e0 : ∀ j, j < 31 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m14]; exact q13_3e0 j hj
  clear q13_3e0 q13_385 q13_27c q13_25c w13_39c w13_398 w13_74 w13_64 w13_4c w13_40 w13_34 w13_20 w13_1c g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_10 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  -- 0x1838: sb
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sb F E14 s14 sv_at_1838 (off' := 0x183C) (c := 0x3A8)
    (by decide) (by rw [g14_2]; sv_addr) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_10 : reg n15 a0 = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [rg15 a0, g14_10]
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
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_1c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := (K15.w32 (by decide) (by decide)).trans w14_1c
  have w15_20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K15.w32 (by decide) (by decide)).trans w14_20
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K15.w32 (by decide) (by decide)).trans w14_34
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K15.w32 (by decide) (by decide)).trans w14_40
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K15.w32 (by decide) (by decide)).trans w14_4c
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K15.w32 (by decide) (by decide)).trans w14_64
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K15.w32 (by decide) (by decide)).trans w14_74
  have w15_398 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := (K15.w32 (by decide) (by decide)).trans w14_398
  have w15_39c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := (K15.w32 (by decide) (by decide)).trans w14_39c
  have b15_3a8 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [W15, g14_10]
  have q15_25c : ∀ j, j < 31 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_25c j hj)
  have q15_27c : ∀ j, j < 19 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_27c j hj)
  have q15_385 : ∀ j, j < 19 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_385 j hj)
  have q15_3e0 : ∀ j, j < 31 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_3e0 j hj)
  clear q14_3e0 q14_385 q14_27c q14_25c w14_39c w14_398 w14_74 w14_64 w14_4c w14_40 w14_34 w14_20 w14_1c g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0x183C
  obtain ⟨n16, c16, u16⟩ := s15.block svCr1e183c E15.self svCr1e183c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem SV n16 0x1844 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock svCr1e183c (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
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
  have g16_10 : reg n16 a0 = B + 0x21A0 + BitVec.ofNat 32 0x3A9 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svCr1e183c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_10, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g16_11 : reg n16 a1 = B + 0x21A0 + BitVec.ofNat 32 0x25C := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svCr1e183c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_10, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g16_12 : reg n16 a2 = BitVec.ofNat 32 0x1F := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svCr1e183c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_10, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_1c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m16]; exact w15_1c
  have w16_20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m16]; exact w15_20
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m16]; exact w15_34
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m16]; exact w15_40
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m16]; exact w15_4c
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m16]; exact w15_64
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m16]; exact w15_74
  have w16_398 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m16]; exact w15_398
  have w16_39c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m16]; exact w15_39c
  have b16_3a8 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m16]; exact b15_3a8
  have q16_25c : ∀ j, j < 31 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m16]; exact q15_25c j hj
  have q16_27c : ∀ j, j < 19 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m16]; exact q15_27c j hj
  have q16_385 : ∀ j, j < 19 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m16]; exact q15_385 j hj
  have q16_3e0 : ∀ j, j < 31 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m16]; exact q15_3e0 j hj
  clear q15_3e0 q15_385 q15_27c q15_25c b15_3a8 w15_39c w15_398 w15_74 w15_64 w15_4c w15_40 w15_34 w15_20 w15_1c g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_10 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  -- 0x1844: memcpy
  obtain ⟨n17, P17, K17, X17⟩ := sv_mc (c := 0x3A9) (d := 0x25C) (N := 0x1F) F E16 s16 sv_at_1844 sv_at_1848
    (by decide) (by decide) g16_2 g16_10 g16_11 g16_12
    (by decide) (by decide) (by decide)
  have s17 := P17.st
  have fr17 := P17.fr
  have t17 : Steps n0 n17 := t16.trans P17.steps
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [P17.regs sp (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P17.regs (3 : Fin 32) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P17.regs (4 : Fin 32) (by decide), g16_4]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [P17.regs (18 : Fin 32) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [P17.regs (19 : Fin 32) (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [P17.regs (20 : Fin 32) (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [P17.regs (21 : Fin 32) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [P17.regs (22 : Fin 32) (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [P17.regs (23 : Fin 32) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by rw [P17.regs (24 : Fin 32) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [P17.regs (25 : Fin 32) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [P17.regs (26 : Fin 32) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [P17.regs (27 : Fin 32) (by decide), g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_1c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := (K17.w32 (by decide) (by decide)).trans w16_1c
  have w17_20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K17.w32 (by decide) (by decide)).trans w16_20
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K17.w32 (by decide) (by decide)).trans w16_34
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K17.w32 (by decide) (by decide)).trans w16_40
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K17.w32 (by decide) (by decide)).trans w16_4c
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K17.w32 (by decide) (by decide)).trans w16_64
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K17.w32 (by decide) (by decide)).trans w16_74
  have w17_398 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := (K17.w32 (by decide) (by decide)).trans w16_398
  have w17_39c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := (K17.w32 (by decide) (by decide)).trans w16_39c
  have b17_3a8 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := (K17.b8 (by decide) (by decide)).trans b16_3a8
  have q17_25c : ∀ j, j < 31 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K17.range (by decide) (by decide) j hj).trans (q16_25c j hj)
  have q17_27c : ∀ j, j < 19 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K17.range (by decide) (by decide) j hj).trans (q16_27c j hj)
  have q17_385 : ∀ j, j < 19 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K17.range (by decide) (by decide) j hj).trans (q16_385 j hj)
  have q17_3e0 : ∀ j, j < 31 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K17.range (by decide) (by decide) j hj).trans (q16_3e0 j hj)
  have q17_3a9 : ∀ j, j < 31 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by
    rw [show 0x3A9 + j = 0x3A9 + (0x0 + j) by omega, X17 (0x0 + j) (by omega),
      show 0x25C + (0x0 + j) = 0x25C + j by omega]; exact q16_25c j (by omega)
  clear q16_3e0 q16_385 q16_27c q16_25c b16_3a8 w16_39c w16_398 w16_74 w16_64 w16_4c w16_40 w16_34 w16_20 w16_1c g16_12 g16_11 g16_10 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
  -- 0x184C: lw outside the stack
  obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_184c (off' := 0x1850) (by decide)
    (by rw [g17_19]; exact a_lih)
  have s18 : St n18.mem SV n18 0x1850 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
  have g18_24 : reg n18 (24 : Fin 32) = lih := by
    rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g17_19, sv_ld fR17 lih_in, hlih]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_1c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m18]; exact w17_1c
  have w18_20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m18]; exact w17_20
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m18]; exact w17_34
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m18]; exact w17_40
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m18]; exact w17_4c
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m18]; exact w17_64
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m18]; exact w17_74
  have w18_398 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m18]; exact w17_398
  have w18_39c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m18]; exact w17_39c
  have b18_3a8 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m18]; exact b17_3a8
  have q18_25c : ∀ j, j < 31 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m18]; exact q17_25c j hj
  have q18_27c : ∀ j, j < 19 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_27c j hj
  have q18_385 : ∀ j, j < 19 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_385 j hj
  have q18_3a9 : ∀ j, j < 31 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m18]; exact q17_3a9 j hj
  have q18_3e0 : ∀ j, j < 31 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m18]; exact q17_3e0 j hj
  clear q17_3a9 q17_3e0 q17_385 q17_27c q17_25c b17_3a8 w17_39c w17_398 w17_74 w17_64 w17_4c w17_40 w17_34 w17_20 w17_1c g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 s17 X17 K17 P17
  -- 0x1850: lw outside the stack
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_1850 (off' := 0x1854) (by decide)
    (by rw [g18_19]; exact a_lil)
  have s19 : St n19.mem SV n19 0x1854 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
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
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = lih := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_21 : reg n19 (21 : Fin 32) = lil := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_19, sv_ld fR18 lil_in, hlil]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_1c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m19]; exact w18_1c
  have w19_20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m19]; exact w18_20
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m19]; exact w18_34
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m19]; exact w18_40
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m19]; exact w18_4c
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m19]; exact w18_64
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m19]; exact w18_74
  have w19_398 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m19]; exact w18_398
  have w19_39c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m19]; exact w18_39c
  have b19_3a8 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m19]; exact b18_3a8
  have q19_25c : ∀ j, j < 31 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m19]; exact q18_25c j hj
  have q19_27c : ∀ j, j < 19 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_27c j hj
  have q19_385 : ∀ j, j < 19 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_385 j hj
  have q19_3a9 : ∀ j, j < 31 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m19]; exact q18_3a9 j hj
  have q19_3e0 : ∀ j, j < 31 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m19]; exact q18_3e0 j hj
  clear q18_3e0 q18_3a9 q18_385 q18_27c q18_25c b18_3a8 w18_39c w18_398 w18_74 w18_64 w18_4c w18_40 w18_34 w18_20 w18_1c g18_24 g18_27 g18_26 g18_25 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x1854: lw
  obtain ⟨n20, d20, u20⟩ := s19.lw E19.self sv_at_1854 (off' := 0x1856) (by decide)
    (by rw [g19_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s20 : St n20.mem SV n20 0x1856 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_4]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, upd_ne (by decide) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = lil := by rw [u20.regs, upd_ne (by decide) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = lih := by rw [u20.regs, upd_ne (by decide) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_27]
  have g20_10 : reg n20 a0 = w40 := by
    rw [u20.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g19_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr, w19_40]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_1c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m20]; exact w19_1c
  have w20_20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m20]; exact w19_20
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m20]; exact w19_34
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m20]; exact w19_40
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m20]; exact w19_4c
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m20]; exact w19_64
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m20]; exact w19_74
  have w20_398 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m20]; exact w19_398
  have w20_39c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m20]; exact w19_39c
  have b20_3a8 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m20]; exact b19_3a8
  have q20_25c : ∀ j, j < 31 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m20]; exact q19_25c j hj
  have q20_27c : ∀ j, j < 19 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_27c j hj
  have q20_385 : ∀ j, j < 19 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_385 j hj
  have q20_3a9 : ∀ j, j < 31 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m20]; exact q19_3a9 j hj
  have q20_3e0 : ∀ j, j < 31 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m20]; exact q19_3e0 j hj
  clear q19_3e0 q19_3a9 q19_385 q19_27c q19_25c b19_3a8 w19_39c w19_398 w19_74 w19_64 w19_4c w19_40 w19_34 w19_20 w19_1c g19_21 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_20 g19_19 g19_18 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x1856
  obtain ⟨n21, c21, u21⟩ := s20.block svCr1e1856 E20.self svCr1e1856_end
    ⟨trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x1858 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svCr1e1856 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by
    rw [rb21, runBlock_reg _ _ _ sp s20.zero (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (3 : Fin 32) s20.zero (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (4 : Fin 32) s20.zero (by decide), g20_4]
  have g21_10 : reg n21 a0 = w40 := by
    rw [rb21, runBlock_reg _ _ _ a0 s20.zero (by decide), g20_10]
  have g21_18 : reg n21 (18 : Fin 32) = out := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = lil := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by
    rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by
    rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = lih := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_11 : reg n21 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svCr1e1856, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_10, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_1c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m21]; exact w20_1c
  have w21_20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m21]; exact w20_20
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m21]; exact w20_34
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m21]; exact w20_40
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m21]; exact w20_4c
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m21]; exact w20_64
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m21]; exact w20_74
  have w21_398 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m21]; exact w20_398
  have w21_39c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m21]; exact w20_39c
  have b21_3a8 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m21]; exact b20_3a8
  have q21_25c : ∀ j, j < 31 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m21]; exact q20_25c j hj
  have q21_27c : ∀ j, j < 19 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_27c j hj
  have q21_385 : ∀ j, j < 19 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_385 j hj
  have q21_3a9 : ∀ j, j < 31 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m21]; exact q20_3a9 j hj
  have q21_3e0 : ∀ j, j < 31 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m21]; exact q20_3e0 j hj
  clear q20_3e0 q20_3a9 q20_385 q20_27c q20_25c b20_3a8 w20_39c w20_398 w20_74 w20_64 w20_4c w20_40 w20_34 w20_20 w20_1c g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
  -- 0x1858: sw
  obtain ⟨n22, d22, s22, fr22, K22, W22, rg22⟩ := sv_sw F E21 s21 sv_at_1858 (off' := 0x185A) (c := 0x380)
    (by decide) (by rw [g21_11]; sv_addr) (by decide) (by decide)
  have t22 : Steps n0 n22 := t21.trans d22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keep K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [rg22 sp, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg22 (3 : Fin 32), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg22 (4 : Fin 32), g21_4]
  have g22_10 : reg n22 a0 = w40 := by rw [rg22 a0, g21_10]
  have g22_11 : reg n22 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg22 a1, g21_11]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rg22 (18 : Fin 32), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rg22 (19 : Fin 32), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [rg22 (20 : Fin 32), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = lil := by rw [rg22 (21 : Fin 32), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [rg22 (22 : Fin 32), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [rg22 (23 : Fin 32), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = lih := by rw [rg22 (24 : Fin 32), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [rg22 (25 : Fin 32), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [rg22 (26 : Fin 32), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [rg22 (27 : Fin 32), g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4)] := keep_kk21.trans K22.toL
  clear keep_kk21
  have w22_1c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := (K22.w32 (by decide) (by decide)).trans w21_1c
  have w22_20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K22.w32 (by decide) (by decide)).trans w21_20
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K22.w32 (by decide) (by decide)).trans w21_34
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K22.w32 (by decide) (by decide)).trans w21_40
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K22.w32 (by decide) (by decide)).trans w21_4c
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K22.w32 (by decide) (by decide)).trans w21_64
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K22.w32 (by decide) (by decide)).trans w21_74
  have w22_398 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := (K22.w32 (by decide) (by decide)).trans w21_398
  have w22_39c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := (K22.w32 (by decide) (by decide)).trans w21_39c
  have b22_3a8 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := (K22.b8 (by decide) (by decide)).trans b21_3a8
  have w22_380 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := by rw [W22, g21_10]
  have q22_25c : ∀ j, j < 31 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_25c j hj)
  have q22_27c : ∀ j, j < 19 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_27c j hj)
  have q22_385 : ∀ j, j < 19 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_385 j hj)
  have q22_3a9 : ∀ j, j < 31 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_3a9 j hj)
  have q22_3e0 : ∀ j, j < 31 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_3e0 j hj)
  clear q21_3e0 q21_3a9 q21_385 q21_27c q21_25c b21_3a8 w21_39c w21_398 w21_74 w21_64 w21_4c w21_40 w21_34 w21_20 w21_1c g21_11 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_10 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x185A: sb
  obtain ⟨n23, d23, s23, fr23, K23, W23, rg23⟩ := sv_sb F E22 s22 sv_at_185a (off' := 0x185E) (c := 0x384)
    (by decide) (by rw [g22_2]; sv_addr) (by decide)
  have t23 : Steps n0 n23 := t22.trans d23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.keep K23 (by decide)
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [rg23 sp, g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg23 (3 : Fin 32), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg23 (4 : Fin 32), g22_4]
  have g23_10 : reg n23 a0 = w40 := by rw [rg23 a0, g22_10]
  have g23_11 : reg n23 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg23 a1, g22_11]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [rg23 (18 : Fin 32), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [rg23 (19 : Fin 32), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [rg23 (20 : Fin 32), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = lil := by rw [rg23 (21 : Fin 32), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [rg23 (22 : Fin 32), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [rg23 (23 : Fin 32), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = lih := by rw [rg23 (24 : Fin 32), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [rg23 (25 : Fin 32), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [rg23 (26 : Fin 32), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [rg23 (27 : Fin 32), g22_27]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1)] := keep_kk22.trans K23.toL
  clear keep_kk22
  have w23_1c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := (K23.w32 (by decide) (by decide)).trans w22_1c
  have w23_20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K23.w32 (by decide) (by decide)).trans w22_20
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K23.w32 (by decide) (by decide)).trans w22_34
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K23.w32 (by decide) (by decide)).trans w22_40
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K23.w32 (by decide) (by decide)).trans w22_4c
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K23.w32 (by decide) (by decide)).trans w22_64
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K23.w32 (by decide) (by decide)).trans w22_74
  have w23_380 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := (K23.w32 (by decide) (by decide)).trans w22_380
  have w23_398 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := (K23.w32 (by decide) (by decide)).trans w22_398
  have w23_39c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := (K23.w32 (by decide) (by decide)).trans w22_39c
  have b23_3a8 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := (K23.b8 (by decide) (by decide)).trans b22_3a8
  have b23_384 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := by rw [W23, g22_25]
  have q23_25c : ∀ j, j < 31 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_25c j hj)
  have q23_27c : ∀ j, j < 19 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_27c j hj)
  have q23_385 : ∀ j, j < 19 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_385 j hj)
  have q23_3a9 : ∀ j, j < 31 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_3a9 j hj)
  have q23_3e0 : ∀ j, j < 31 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_3e0 j hj)
  clear q22_3e0 q22_3a9 q22_385 q22_27c q22_25c w22_380 b22_3a8 w22_39c w22_398 w22_74 w22_64 w22_4c w22_40 w22_34 w22_20 w22_1c g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_11 g22_10 g22_4 g22_3 g22_2 V22 E22 fR22 t22 rg22 W22 K22 fr22 s22 d22
  -- 0x185E: lw
  obtain ⟨n24, d24, u24⟩ := s23.lw E23.self sv_at_185e (off' := 0x1860) (by decide)
    (by rw [g23_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s24 : St n24.mem SV n24 0x1860 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_4]
  have g24_11 : reg n24 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_11]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, upd_ne (by decide) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = lil := by rw [u24.regs, upd_ne (by decide) (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = lih := by rw [u24.regs, upd_ne (by decide) (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_27]
  have g24_10 : reg n24 a0 = w64 := by
    rw [u24.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g23_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr, w23_64]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_1c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m24]; exact w23_1c
  have w24_20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m24]; exact w23_20
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m24]; exact w23_34
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m24]; exact w23_40
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m24]; exact w23_4c
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m24]; exact w23_64
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m24]; exact w23_74
  have w24_380 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := by rw [m24]; exact w23_380
  have w24_398 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m24]; exact w23_398
  have w24_39c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m24]; exact w23_39c
  have b24_384 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := by rw [m24]; exact b23_384
  have b24_3a8 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m24]; exact b23_3a8
  have q24_25c : ∀ j, j < 31 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m24]; exact q23_25c j hj
  have q24_27c : ∀ j, j < 19 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_27c j hj
  have q24_385 : ∀ j, j < 19 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_385 j hj
  have q24_3a9 : ∀ j, j < 31 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m24]; exact q23_3a9 j hj
  have q24_3e0 : ∀ j, j < 31 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m24]; exact q23_3e0 j hj
  clear q23_3e0 q23_3a9 q23_385 q23_27c q23_25c b23_384 b23_3a8 w23_39c w23_398 w23_380 w23_74 w23_64 w23_4c w23_40 w23_34 w23_20 w23_1c g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_11 g23_10 g23_4 g23_3 g23_2 V23 E23 fR23 t23 rg23 W23 K23 fr23 s23 d23
  -- 0x1860: sw
  obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_1860 (off' := 0x1862) (c := 0x3A0)
    (by decide) (by rw [g24_11]; sv_addr) (by decide) (by decide)
  have t25 : Steps n0 n25 := t24.trans d25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
  have g25_10 : reg n25 a0 = w64 := by rw [rg25 a0, g24_10]
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg25 a1, g24_11]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [rg25 (20 : Fin 32), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = lil := by rw [rg25 (21 : Fin 32), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [rg25 (22 : Fin 32), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [rg25 (23 : Fin 32), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = lih := by rw [rg25 (24 : Fin 32), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rg25 (25 : Fin 32), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rg25 (26 : Fin 32), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = x27 := by rw [rg25 (27 : Fin 32), g24_27]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4)] := keep_kk24.trans K25.toL
  clear keep_kk24
  have w25_1c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := (K25.w32 (by decide) (by decide)).trans w24_1c
  have w25_20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K25.w32 (by decide) (by decide)).trans w24_20
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K25.w32 (by decide) (by decide)).trans w24_34
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K25.w32 (by decide) (by decide)).trans w24_40
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K25.w32 (by decide) (by decide)).trans w24_4c
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K25.w32 (by decide) (by decide)).trans w24_64
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K25.w32 (by decide) (by decide)).trans w24_74
  have w25_380 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := (K25.w32 (by decide) (by decide)).trans w24_380
  have w25_398 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := (K25.w32 (by decide) (by decide)).trans w24_398
  have w25_39c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := (K25.w32 (by decide) (by decide)).trans w24_39c
  have b25_384 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_384
  have b25_3a8 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_3a8
  have w25_3a0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 := by rw [W25, g24_10]
  have q25_25c : ∀ j, j < 31 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_25c j hj)
  have q25_27c : ∀ j, j < 19 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_27c j hj)
  have q25_385 : ∀ j, j < 19 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_385 j hj)
  have q25_3a9 : ∀ j, j < 31 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_3a9 j hj)
  have q25_3e0 : ∀ j, j < 31 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_3e0 j hj)
  clear q24_3e0 q24_3a9 q24_385 q24_27c q24_25c b24_3a8 b24_384 w24_39c w24_398 w24_380 w24_74 w24_64 w24_4c w24_40 w24_34 w24_20 w24_1c g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_11 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x1862: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_1862 (off' := 0x1864) (by decide)
    (by rw [g25_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0x1864 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_11 : reg n26 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_11]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = lil := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = lih := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_10 : reg n26 a0 = w74 := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr, w25_74]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_1c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m26]; exact w25_1c
  have w26_20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m26]; exact w25_20
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m26]; exact w25_34
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m26]; exact w25_40
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m26]; exact w25_4c
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m26]; exact w25_64
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m26]; exact w25_74
  have w26_380 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := by rw [m26]; exact w25_380
  have w26_398 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m26]; exact w25_398
  have w26_39c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m26]; exact w25_39c
  have w26_3a0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 := by rw [m26]; exact w25_3a0
  have b26_384 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := by rw [m26]; exact b25_384
  have b26_3a8 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m26]; exact b25_3a8
  have q26_25c : ∀ j, j < 31 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m26]; exact q25_25c j hj
  have q26_27c : ∀ j, j < 19 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m26]; exact q25_27c j hj
  have q26_385 : ∀ j, j < 19 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m26]; exact q25_385 j hj
  have q26_3a9 : ∀ j, j < 31 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m26]; exact q25_3a9 j hj
  have q26_3e0 : ∀ j, j < 31 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m26]; exact q25_3e0 j hj
  clear q25_3e0 q25_3a9 q25_385 q25_27c q25_25c w25_3a0 b25_3a8 b25_384 w25_39c w25_398 w25_380 w25_74 w25_64 w25_4c w25_40 w25_34 w25_20 w25_1c g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_11 g25_10 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
  -- 0x1864: sw
  obtain ⟨n27, d27, s27, fr27, K27, W27, rg27⟩ := sv_sw F E26 s26 sv_at_1864 (off' := 0x1866) (c := 0x3A4)
    (by decide) (by rw [g26_11]; sv_addr) (by decide) (by decide)
  have t27 : Steps n0 n27 := t26.trans d27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keep K27 (by decide)
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rg27 sp, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg27 (3 : Fin 32), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg27 (4 : Fin 32), g26_4]
  have g27_10 : reg n27 a0 = w74 := by rw [rg27 a0, g26_10]
  have g27_11 : reg n27 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg27 a1, g26_11]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rg27 (18 : Fin 32), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rg27 (19 : Fin 32), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [rg27 (20 : Fin 32), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = lil := by rw [rg27 (21 : Fin 32), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [rg27 (22 : Fin 32), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [rg27 (23 : Fin 32), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = lih := by rw [rg27 (24 : Fin 32), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [rg27 (25 : Fin 32), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [rg27 (26 : Fin 32), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [rg27 (27 : Fin 32), g26_27]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4)] := keep_kk26.trans K27.toL
  clear keep_kk26
  have w27_1c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := (K27.w32 (by decide) (by decide)).trans w26_1c
  have w27_20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K27.w32 (by decide) (by decide)).trans w26_20
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K27.w32 (by decide) (by decide)).trans w26_34
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K27.w32 (by decide) (by decide)).trans w26_40
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K27.w32 (by decide) (by decide)).trans w26_4c
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K27.w32 (by decide) (by decide)).trans w26_64
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K27.w32 (by decide) (by decide)).trans w26_74
  have w27_380 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := (K27.w32 (by decide) (by decide)).trans w26_380
  have w27_398 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := (K27.w32 (by decide) (by decide)).trans w26_398
  have w27_39c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := (K27.w32 (by decide) (by decide)).trans w26_39c
  have w27_3a0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 := (K27.w32 (by decide) (by decide)).trans w26_3a0
  have b27_384 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_384
  have b27_3a8 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_3a8
  have w27_3a4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74 := by rw [W27, g26_10]
  have q27_25c : ∀ j, j < 31 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_25c j hj)
  have q27_27c : ∀ j, j < 19 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_27c j hj)
  have q27_385 : ∀ j, j < 19 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_385 j hj)
  have q27_3a9 : ∀ j, j < 31 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_3a9 j hj)
  have q27_3e0 : ∀ j, j < 31 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_3e0 j hj)
  clear q26_3e0 q26_3a9 q26_385 q26_27c q26_25c b26_3a8 b26_384 w26_3a0 w26_39c w26_398 w26_380 w26_74 w26_64 w26_4c w26_40 w26_34 w26_20 w26_1c g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_11 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0x1866: branch, taken
  obtain ⟨n28, d28, u28⟩ := s27.taken E27.self 0x1890 sv_at_1866
    (by decide) (by rw [g27_24, g27_10]; exact br_beq_t hhi)
  have s28 : St n28.mem SV n28 0x1890 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
  have g28_10 : reg n28 a0 = w74 := by rw [u28.regs, g27_10]
  have g28_11 : reg n28 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [u28.regs, g27_11]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = lil := by rw [u28.regs, g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = lih := by rw [u28.regs, g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [u28.regs, g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_1c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m28]; exact w27_1c
  have w28_20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m28]; exact w27_20
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m28]; exact w27_34
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m28]; exact w27_40
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m28]; exact w27_4c
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m28]; exact w27_64
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m28]; exact w27_74
  have w28_380 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := by rw [m28]; exact w27_380
  have w28_398 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m28]; exact w27_398
  have w28_39c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m28]; exact w27_39c
  have w28_3a0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 := by rw [m28]; exact w27_3a0
  have w28_3a4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74 := by rw [m28]; exact w27_3a4
  have b28_384 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := by rw [m28]; exact b27_384
  have b28_3a8 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m28]; exact b27_3a8
  have q28_25c : ∀ j, j < 31 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m28]; exact q27_25c j hj
  have q28_27c : ∀ j, j < 19 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_27c j hj
  have q28_385 : ∀ j, j < 19 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_385 j hj
  have q28_3a9 : ∀ j, j < 31 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m28]; exact q27_3a9 j hj
  have q28_3e0 : ∀ j, j < 31 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m28]; exact q27_3e0 j hj
  clear q27_3e0 q27_3a9 q27_385 q27_27c q27_25c w27_3a4 b27_3a8 b27_384 w27_3a0 w27_39c w27_398 w27_380 w27_74 w27_64 w27_4c w27_40 w27_34 w27_20 w27_1c g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_11 g27_10 g27_4 g27_3 g27_2 V27 E27 fR27 t27 rg27 W27 K27 fr27 s27 d27
  -- 0x1890: lw
  obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_1890 (off' := 0x1892) (by decide)
    (by rw [g28_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s29 : St n29.mem SV n29 0x1892 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
  have g29_11 : reg n29 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_11]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = lil := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = lih := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = x27 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
  have g29_10 : reg n29 a0 = w64 := by
    rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g28_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr, w28_64]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_1c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m29]; exact w28_1c
  have w29_20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m29]; exact w28_20
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m29]; exact w28_34
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m29]; exact w28_40
  have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m29]; exact w28_4c
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m29]; exact w28_64
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m29]; exact w28_74
  have w29_380 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := by rw [m29]; exact w28_380
  have w29_398 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m29]; exact w28_398
  have w29_39c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m29]; exact w28_39c
  have w29_3a0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 := by rw [m29]; exact w28_3a0
  have w29_3a4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74 := by rw [m29]; exact w28_3a4
  have b29_384 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := by rw [m29]; exact b28_384
  have b29_3a8 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m29]; exact b28_3a8
  have q29_25c : ∀ j, j < 31 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m29]; exact q28_25c j hj
  have q29_27c : ∀ j, j < 19 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_27c j hj
  have q29_385 : ∀ j, j < 19 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_385 j hj
  have q29_3a9 : ∀ j, j < 31 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m29]; exact q28_3a9 j hj
  have q29_3e0 : ∀ j, j < 31 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m29]; exact q28_3e0 j hj
  clear q28_3e0 q28_3a9 q28_385 q28_27c q28_25c b28_3a8 b28_384 w28_3a4 w28_3a0 w28_39c w28_398 w28_380 w28_74 w28_64 w28_4c w28_40 w28_34 w28_20 w28_1c g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_11 g28_10 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  -- 0x1892
  obtain ⟨n30, c30, u30⟩ := s29.block svCr1e1892 E29.self svCr1e1892_end
    ⟨trivial, trivial⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have s30 : St n30.mem SV n30 0x1896 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have rb30 : ∀ q, reg n30 q = (runBlock svCr1e1892 (n29.mem, reg n29)).2 q := fun q => by rw [u30.regs]
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans c30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by
    rw [rb30, runBlock_reg _ _ _ sp s29.zero (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb30, runBlock_reg _ _ _ (3 : Fin 32) s29.zero (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb30, runBlock_reg _ _ _ (4 : Fin 32) s29.zero (by decide), g29_4]
  have g30_11 : reg n30 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb30, runBlock_reg _ _ _ a1 s29.zero (by decide), g29_11]
  have g30_18 : reg n30 (18 : Fin 32) = out := by
    rw [rb30, runBlock_reg _ _ _ (18 : Fin 32) s29.zero (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by
    rw [rb30, runBlock_reg _ _ _ (19 : Fin 32) s29.zero (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by
    rw [rb30, runBlock_reg _ _ _ (20 : Fin 32) s29.zero (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = lil := by
    rw [rb30, runBlock_reg _ _ _ (21 : Fin 32) s29.zero (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by
    rw [rb30, runBlock_reg _ _ _ (22 : Fin 32) s29.zero (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by
    rw [rb30, runBlock_reg _ _ _ (23 : Fin 32) s29.zero (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = lih := by
    rw [rb30, runBlock_reg _ _ _ (24 : Fin 32) s29.zero (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by
    rw [rb30, runBlock_reg _ _ _ (25 : Fin 32) s29.zero (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by
    rw [rb30, runBlock_reg _ _ _ (26 : Fin 32) s29.zero (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = x27 := by
    rw [rb30, runBlock_reg _ _ _ (27 : Fin 32) s29.zero (by decide), g29_27]
  have g30_10 : reg n30 a0 = aluEval .sltu (lil) (w64) := by
    rw [rb30]; simp +decide only [runBlock, BInstr.run, svCr1e1892, upd, ↓reduceIte]; rw [g29_21, g29_10] <;> rfl
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_1c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m30]; exact w29_1c
  have w30_20 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m30]; exact w29_20
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m30]; exact w29_34
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m30]; exact w29_40
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m30]; exact w29_4c
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m30]; exact w29_64
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m30]; exact w29_74
  have w30_380 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := by rw [m30]; exact w29_380
  have w30_398 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m30]; exact w29_398
  have w30_39c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m30]; exact w29_39c
  have w30_3a0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 := by rw [m30]; exact w29_3a0
  have w30_3a4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74 := by rw [m30]; exact w29_3a4
  have b30_384 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := by rw [m30]; exact b29_384
  have b30_3a8 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m30]; exact b29_3a8
  have q30_25c : ∀ j, j < 31 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m30]; exact q29_25c j hj
  have q30_27c : ∀ j, j < 19 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m30]; exact q29_27c j hj
  have q30_385 : ∀ j, j < 19 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m30]; exact q29_385 j hj
  have q30_3a9 : ∀ j, j < 31 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m30]; exact q29_3a9 j hj
  have q30_3e0 : ∀ j, j < 31 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m30]; exact q29_3e0 j hj
  clear q29_3e0 q29_3a9 q29_385 q29_27c q29_25c b29_3a8 b29_384 w29_3a4 w29_3a0 w29_39c w29_398 w29_380 w29_74 w29_64 w29_4c w29_40 w29_34 w29_20 w29_1c g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  by_cases hidx : aluEval .sltu (lil) (w64) ≠ 0
  rotate_left
  · -- 0x1896: branch, taken
    obtain ⟨n31, d31, u31⟩ := s30.taken E30.self 0x19A2 sv_at_1896
      (by decide) (by rw [g30_10, s30.zero]; exact br_beq_t (Decidable.of_not_not hidx))
    have s31 : St n31.mem SV n31 0x19A2 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, g30_4]
    have g31_10 : reg n31 a0 = aluEval .sltu (lil) (w64) := by rw [u31.regs, g30_10]
    have g31_11 : reg n31 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [u31.regs, g30_11]
    have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [u31.regs, g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = lil := by rw [u31.regs, g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [u31.regs, g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = lih := by rw [u31.regs, g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = x25 := by rw [u31.regs, g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [u31.regs, g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = x27 := by rw [u31.regs, g30_27]
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_1c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m31]; exact w30_1c
    have w31_20 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m31]; exact w30_20
    have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m31]; exact w30_34
    have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m31]; exact w30_40
    have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m31]; exact w30_4c
    have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m31]; exact w30_64
    have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m31]; exact w30_74
    have w31_380 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := by rw [m31]; exact w30_380
    have w31_398 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m31]; exact w30_398
    have w31_39c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m31]; exact w30_39c
    have w31_3a0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 := by rw [m31]; exact w30_3a0
    have w31_3a4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74 := by rw [m31]; exact w30_3a4
    have b31_384 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := by rw [m31]; exact b30_384
    have b31_3a8 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m31]; exact b30_3a8
    have q31_25c : ∀ j, j < 31 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_25c j hj
    have q31_27c : ∀ j, j < 19 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_27c j hj
    have q31_385 : ∀ j, j < 19 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_385 j hj
    have q31_3a9 : ∀ j, j < 31 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_3a9 j hj
    have q31_3e0 : ∀ j, j < 31 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_3e0 j hj
    clear q30_3e0 q30_3a9 q30_385 q30_27c q30_25c b30_3a8 b30_384 w30_3a4 w30_3a0 w30_39c w30_398 w30_380 w30_74 w30_64 w30_4c w30_40 w30_34 w30_20 w30_1c g30_10 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_11 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 rb30 s30 m30 u30 c30
    -- 0x19A2
    obtain ⟨n32, c32, u32⟩ := s31.block svCr1e19a2 E31.self svCr1e19a2_end
      ⟨trivial, trivial, trivial⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have s32 : St n32.mem SV n32 0x19A8 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have rb32 : ∀ q, reg n32 q = (runBlock svCr1e19a2 (n31.mem, reg n31)).2 q := fun q => by rw [u32.regs]
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans c32
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by
      rw [rb32, runBlock_reg _ _ _ sp s31.zero (by decide), g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb32, runBlock_reg _ _ _ (3 : Fin 32) s31.zero (by decide), g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb32, runBlock_reg _ _ _ (4 : Fin 32) s31.zero (by decide), g31_4]
    have g32_11 : reg n32 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
      rw [rb32, runBlock_reg _ _ _ a1 s31.zero (by decide), g31_11]
    have g32_18 : reg n32 (18 : Fin 32) = out := by
      rw [rb32, runBlock_reg _ _ _ (18 : Fin 32) s31.zero (by decide), g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by
      rw [rb32, runBlock_reg _ _ _ (19 : Fin 32) s31.zero (by decide), g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = x20 := by
      rw [rb32, runBlock_reg _ _ _ (20 : Fin 32) s31.zero (by decide), g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = lil := by
      rw [rb32, runBlock_reg _ _ _ (21 : Fin 32) s31.zero (by decide), g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = x22 := by
      rw [rb32, runBlock_reg _ _ _ (22 : Fin 32) s31.zero (by decide), g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = x23 := by
      rw [rb32, runBlock_reg _ _ _ (23 : Fin 32) s31.zero (by decide), g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = lih := by
      rw [rb32, runBlock_reg _ _ _ (24 : Fin 32) s31.zero (by decide), g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = x25 := by
      rw [rb32, runBlock_reg _ _ _ (25 : Fin 32) s31.zero (by decide), g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = x26 := by
      rw [rb32, runBlock_reg _ _ _ (26 : Fin 32) s31.zero (by decide), g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = x27 := by
      rw [rb32, runBlock_reg _ _ _ (27 : Fin 32) s31.zero (by decide), g31_27]
    have g32_10 : reg n32 a0 = BitVec.ofNat 32 0x1B01 := by
      rw [rb32]; simp +decide only [runBlock, BInstr.run, svCr1e19a2, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g31_2, g31_3, g31_4, g31_10, g31_11, g31_18, g31_19, g31_20, g31_21, g31_22, g31_23, g31_24, g31_25, g31_26, g31_27, s31.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_1c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m32]; exact w31_1c
    have w32_20 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m32]; exact w31_20
    have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m32]; exact w31_34
    have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m32]; exact w31_40
    have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m32]; exact w31_4c
    have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m32]; exact w31_64
    have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m32]; exact w31_74
    have w32_380 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := by rw [m32]; exact w31_380
    have w32_398 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m32]; exact w31_398
    have w32_39c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m32]; exact w31_39c
    have w32_3a0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 := by rw [m32]; exact w31_3a0
    have w32_3a4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74 := by rw [m32]; exact w31_3a4
    have b32_384 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := by rw [m32]; exact b31_384
    have b32_3a8 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m32]; exact b31_3a8
    have q32_25c : ∀ j, j < 31 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m32]; exact q31_25c j hj
    have q32_27c : ∀ j, j < 19 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_27c j hj
    have q32_385 : ∀ j, j < 19 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_385 j hj
    have q32_3a9 : ∀ j, j < 31 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m32]; exact q31_3a9 j hj
    have q32_3e0 : ∀ j, j < 31 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m32]; exact q31_3e0 j hj
    clear q31_3e0 q31_3a9 q31_385 q31_27c q31_25c b31_3a8 b31_384 w31_3a4 w31_3a0 w31_39c w31_398 w31_380 w31_74 w31_64 w31_4c w31_40 w31_34 w31_20 w31_1c g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_11 g31_10 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    -- 0x19A8: j
    obtain ⟨n33, d33, u33⟩ := s32.jump E32.self sv_at_19a8 (off' := 0x138E) (by decide)
      (by rw [s32.pc]; decide)
    have s33 : St n33.mem SV n33 0x138E (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
    have m33 : n33.mem = n32.mem := u33.mem
    have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
    have t33 : Steps n0 n33 := t32.trans (.single d33)
    have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
    have E33 : SvCode n33.mem := E32.fr F fr33
    have V33 : SvSaves B n33.mem v := V32.same m33
    have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
    have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
    have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
    have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x1B01 := by rw [u33.regs, g32_10]
    have g33_11 : reg n33 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [u33.regs, g32_11]
    have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
    have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
    have g33_20 : reg n33 (20 : Fin 32) = x20 := by rw [u33.regs, g32_20]
    have g33_21 : reg n33 (21 : Fin 32) = lil := by rw [u33.regs, g32_21]
    have g33_22 : reg n33 (22 : Fin 32) = x22 := by rw [u33.regs, g32_22]
    have g33_23 : reg n33 (23 : Fin 32) = x23 := by rw [u33.regs, g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = lih := by rw [u33.regs, g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = x25 := by rw [u33.regs, g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [u33.regs, g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = x27 := by rw [u33.regs, g32_27]
    have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4)] := by rw [m33]; exact keep_kk32
    clear keep_kk32
    have w33_1c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m33]; exact w32_1c
    have w33_20 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m33]; exact w32_20
    have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m33]; exact w32_34
    have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m33]; exact w32_40
    have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m33]; exact w32_4c
    have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m33]; exact w32_64
    have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m33]; exact w32_74
    have w33_380 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := by rw [m33]; exact w32_380
    have w33_398 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m33]; exact w32_398
    have w33_39c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m33]; exact w32_39c
    have w33_3a0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 := by rw [m33]; exact w32_3a0
    have w33_3a4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74 := by rw [m33]; exact w32_3a4
    have b33_384 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := by rw [m33]; exact b32_384
    have b33_3a8 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m33]; exact b32_3a8
    have q33_25c : ∀ j, j < 31 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m33]; exact q32_25c j hj
    have q33_27c : ∀ j, j < 19 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_27c j hj
    have q33_385 : ∀ j, j < 19 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_385 j hj
    have q33_3a9 : ∀ j, j < 31 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m33]; exact q32_3a9 j hj
    have q33_3e0 : ∀ j, j < 31 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m33]; exact q32_3e0 j hj
    clear q32_3e0 q32_3a9 q32_385 q32_27c q32_25c b32_3a8 b32_384 w32_3a4 w32_3a0 w32_39c w32_398 w32_380 w32_74 w32_64 w32_4c w32_40 w32_34 w32_20 w32_1c g32_10 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 rb32 s32 m32 u32 c32
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hidx h0'), sv_fail_138e F E33 s33 t33 (fun x hx => (fR33 x hx).trans (fM x hx).symm) V33 hret g33_2 g33_18 hO g33_3 g33_4 (by rw [g33_10]; decide) (by rw [g33_10]; decide)⟩
  -- 0x1896: branch, not taken
  obtain ⟨n31, d31, u31⟩ := s30.notTaken E30.self 0x189A sv_at_1896
    (by decide) (by rw [g30_10, s30.zero]; exact br_beq_f hidx)
  have s31 : St n31.mem SV n31 0x189A (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, g30_4]
  have g31_10 : reg n31 a0 = aluEval .sltu (lil) (w64) := by rw [u31.regs, g30_10]
  have g31_11 : reg n31 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [u31.regs, g30_11]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [u31.regs, g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = lil := by rw [u31.regs, g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [u31.regs, g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = lih := by rw [u31.regs, g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = x25 := by rw [u31.regs, g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [u31.regs, g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = x27 := by rw [u31.regs, g30_27]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_1c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c := by rw [m31]; exact w30_1c
  have w31_20 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m31]; exact w30_20
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m31]; exact w30_34
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m31]; exact w30_40
  have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m31]; exact w30_4c
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m31]; exact w30_64
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m31]; exact w30_74
  have w31_380 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 := by rw [m31]; exact w30_380
  have w31_398 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp := by rw [m31]; exact w30_398
  have w31_39c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c := by rw [m31]; exact w30_39c
  have w31_3a0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 := by rw [m31]; exact w30_3a0
  have w31_3a4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74 := by rw [m31]; exact w30_3a4
  have b31_384 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 := by rw [m31]; exact b30_384
  have b31_3a8 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m31]; exact b30_3a8
  have q31_25c : ∀ j, j < 31 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_25c j hj
  have q31_27c : ∀ j, j < 19 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_27c j hj
  have q31_385 : ∀ j, j < 19 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_385 j hj
  have q31_3a9 : ∀ j, j < 31 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_3a9 j hj
  have q31_3e0 : ∀ j, j < 31 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_3e0 j hj
  clear q30_3e0 q30_3a9 q30_385 q30_27c q30_25c b30_3a8 b30_384 w30_3a4 w30_3a0 w30_39c w30_398 w30_380 w30_74 w30_64 w30_4c w30_40 w30_34 w30_20 w30_1c g30_10 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_11 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 rb30 s30 m30 u30 c30
  exact .inr ⟨hidx, n31, t31, s31, E31, V31, fR31, g31_2, g31_3, g31_4, g31_18, g31_19, g31_20, g31_21, g31_22, g31_23, g31_24, g31_25, g31_26, g31_27, w31_1c, w31_20, w31_34, w31_40, w31_4c, w31_64, w31_74, w31_380, w31_398, w31_39c, w31_3a0, w31_3a4, b31_384, b31_3a8, q31_25c, q31_27c, q31_385, q31_3a9, q31_3e0, keep_kk31.mono (by decide)⟩

end C3.RV32.Sv
