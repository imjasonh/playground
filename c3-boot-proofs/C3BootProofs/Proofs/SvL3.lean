import C3BootProofs.Proofs.SvCongr
import C3BootProofs.Image.BootloaderData3

/-!
# `sigstore::verify`: the serial number and the signature algorithm

From the serial number at 0x1C8 to 0x266: the serial number, a positive integer of at most 20 bytes, and the signature algorithm, which must be ecdsa-with-SHA384 with no parameters.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL31c8 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .aluImm .add a1 sp 0x178]
theorem svL31c8_end : blockEnd sigstoreVerifyCode 0x1C8 svL31c8 = some 0x1D2 := by
  simp only [svL31c8]
  rw [blockEnd, sv_at_1c8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL31e6 : List BInstr :=
  [.aluImm .add a1 x0 0x14]
theorem svL31e6_end : blockEnd sigstoreVerifyCode 0x1E6 svL31e6 = some 0x1E8 := by
  simp only [svL31e6]
  rw [blockEnd, sv_at_1e6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL31ec : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .aluImm .add a1 sp 0x178, .aluImm .add a2 x0 0x30]
theorem svL31ec_end : blockEnd sigstoreVerifyCode 0x1EC svL31ec = some 0x1FA := by
  simp only [svL31ec]
  rw [blockEnd, sv_at_1ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1f0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1f4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1f6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL3222 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .lui a1 0x1000, .aluImm .add a1 a1 0x20, .alu .add a1 a1 sp]
theorem svL3222_end : blockEnd sigstoreVerifyCode 0x222 svL3222 = some 0x232 := by
  simp only [svL3222]
  rw [blockEnd, sv_at_222]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_226]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_22a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_22c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_230]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL3246 : List BInstr :=
  [.alu .add a2 x0 (27 : Fin 32)]
theorem svL3246_end : blockEnd sigstoreVerifyCode 0x246 svL3246 = some 0x248 := by
  simp only [svL3246]
  rw [blockEnd, sv_at_246]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL324c : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF840, .aluImm .add a3 x0 0x8]
theorem svL324c_end : blockEnd sigstoreVerifyCode 0x24C svL324c = some 0x256 := by
  simp only [svL324c]
  rw [blockEnd, sv_at_24c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_250]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_254]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_l3 {B out bp rootp dg lp ll rp rl sgl orl orp trl trp tcl sgp : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x1C8 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = trl)
    (g0_9 : reg n0 (9 : Fin 32) = trp)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = lp)
    (g0_22 : reg n0 (22 : Fin 32) = orp)
    (g0_23 : reg n0 (23 : Fin 32) = tcl)
    (g0_24 : reg n0 (24 : Fin 32) = sgl)
    (g0_25 : reg n0 (25 : Fin 32) = orl)
    (g0_26 : reg n0 (26 : Fin 32) = ll)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg)
    (w0_180 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp)
    (w0_184 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl)
    (tb_in : SvIn B (rp) (rl).toNat) :
    (¬ (∃ tl2, derElement 2 (memBytes M0 (rp) (rl).toNat) = .ok tl2 ∧ ∃ ip2 il2, derPosIntOf (memBytes M0 (rp) (rl).toNat) (rp) (.ok tl2) = .ok (ip2, il2) ∧ ((il2).toNat ≤ 20) ∧ ∃ tl9, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = .ok tl9 ∧ ∃ op19 ol19, derAlgOf M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) (tl9.header + tl9.len) = .ok ((op19, ol19), none) ∧ (memBytes M0 op19 ol19 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x28)) 8) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl2, derElement 2 (memBytes M0 (rp) (rl).toNat) = .ok tl2 ∧
    ∃ ip2 il2, derPosIntOf (memBytes M0 (rp) (rl).toNat) (rp) (.ok tl2) = .ok (ip2, il2) ∧
    ((il2).toNat ≤ 20) ∧
    ∃ tl9, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = .ok tl9 ∧
    ∃ op19 ol19, derAlgOf M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) (tl9.header + tl9.len) = .ok ((op19, ol19), none) ∧
    (memBytes M0 op19 ol19 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x28)) 8) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x266 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = 0 ∧
        reg n' (9 : Fin 32) = trp ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = lp ∧
        reg n' (22 : Fin 32) = orp ∧
        reg n' (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧
        reg n' (24 : Fin 32) = sgl ∧
        reg n' (25 : Fin 32) = orl ∧
        reg n' (26 : Fin 32) = ll ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) ∧
        SvKeepL B n0.mem n'.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x1C8
  obtain ⟨n1, c1, u1⟩ := s0.block svL31c8 E0.self svL31c8_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x1D2 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svL31c8 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_8 : reg n1 (8 : Fin 32) = trl := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = trp := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = lp := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = orp := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = tcl := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = sgl := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = orl := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = ll := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svL31c8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x178 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svL31c8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m1]; exact w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m1]; exact w0_7c
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m1]; exact w0_80
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m1]; exact w0_84
  have w1_180 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m1]; exact w0_180
  have w1_184 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m1]; exact w0_184
  -- 0x1D2: sv_posF
  obtain ⟨n2, c2, s2, sp2, rk2, K2, A2, Ok2, Er2, fr2⟩ := sv_posF (oc := 0xA20) (dc := 0x178)
    F E1 s1 sv_at_1d2 sv_at_1d6 (by decide) (by decide) g1_2 g1_10 g1_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w1_180 w1_184 tb_in
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keepL K2 (by decide)
  rw [sv_mb fR1 tb_in] at A2 Ok2 Er2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rk2 sp (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk2 (3 : Fin 32) (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk2 (4 : Fin 32) (by decide) (by decide), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = trl := by rw [rk2 (8 : Fin 32) (by decide) (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = trp := by rw [rk2 (9 : Fin 32) (by decide) (by decide), g1_9]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [rk2 (18 : Fin 32) (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [rk2 (19 : Fin 32) (by decide) (by decide), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = lp := by rw [rk2 (21 : Fin 32) (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = orp := by rw [rk2 (22 : Fin 32) (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = tcl := by rw [rk2 (23 : Fin 32) (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = sgl := by rw [rk2 (24 : Fin 32) (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = orl := by rw [rk2 (25 : Fin 32) (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = ll := by rw [rk2 (26 : Fin 32) (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk2 (27 : Fin 32) (by decide) (by decide), g1_27]
  obtain ⟨r2, hr2⟩ : ∃ r, derElement 2 (memBytes M0 (rp) (rl).toNat) = r := ⟨_, rfl⟩
  rcases r2 with er2 | tl2
  · obtain ⟨zhr2, -⟩ := Er2 er2 (by rw [hr2]; rfl)
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0xA20, 0x8), (0x180, 0x8)] := keep_kk1.trans K2
    clear keep_kk1
    have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K2.w32 (by decide) (by decide)).trans w1_78
    have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K2.w32 (by decide) (by decide)).trans w1_7c
    have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K2.w32 (by decide) (by decide)).trans w1_80
    have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K2.w32 (by decide) (by decide)).trans w1_84
    have w2_a20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := zhr2
    clear w1_184 w1_180 w1_84 w1_80 w1_7c w1_78 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0x1DA: lw
    obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_1da (off' := 0x1DE) (by decide)
      (by rw [g2_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s3 : St n3.mem SV n3 0x1DE (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
    have g3_8 : reg n3 (8 : Fin 32) = trl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
    have g3_9 : reg n3 (9 : Fin 32) = trp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
    have g3_21 : reg n3 (21 : Fin 32) = lp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = orp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
    have g3_23 : reg n3 (23 : Fin 32) = tcl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
    have g3_24 : reg n3 (24 : Fin 32) = sgl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
    have g3_25 : reg n3 (25 : Fin 32) = orl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
    have g3_10 : reg n3 a0 = 0 := by
      rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g2_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w2_a20]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m3]; exact w2_78
    have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m3]; exact w2_7c
    have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m3]; exact w2_80
    have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m3]; exact w2_84
    have w3_a20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m3]; exact w2_a20
    clear w2_a20 w2_84 w2_80 w2_7c w2_78 zhr2
    -- 0x1DE: branch, taken
    obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x962 sv_at_1de
      (by decide) (by rw [g3_10, s3.zero]; rfl)
    have s4 : St n4.mem SV n4 0x962 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
    have g4_8 : reg n4 (8 : Fin 32) = trl := by rw [u4.regs, g3_8]
    have g4_9 : reg n4 (9 : Fin 32) = trp := by rw [u4.regs, g3_9]
    have g4_10 : reg n4 a0 = 0 := by rw [u4.regs, g3_10]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
    have g4_21 : reg n4 (21 : Fin 32) = lp := by rw [u4.regs, g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = orp := by rw [u4.regs, g3_22]
    have g4_23 : reg n4 (23 : Fin 32) = tcl := by rw [u4.regs, g3_23]
    have g4_24 : reg n4 (24 : Fin 32) = sgl := by rw [u4.regs, g3_24]
    have g4_25 : reg n4 (25 : Fin 32) = orl := by rw [u4.regs, g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = ll := by rw [u4.regs, g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u4.regs, g3_27]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m4]; exact w3_78
    have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m4]; exact w3_7c
    have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m4]; exact w3_80
    have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m4]; exact w3_84
    have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m4]; exact w3_a20
    clear w3_a20 w3_84 w3_80 w3_7c w3_78 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_19 g3_18 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    -- 0x962: lbu
    obtain ⟨n5, d5, u5⟩ := s4.lbu E4.self sv_at_962 (off' := 0x966) (by decide)
    have s5 : St n5.mem SV n5 0x966 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
    have g5_8 : reg n5 (8 : Fin 32) = trl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_8]
    have g5_9 : reg n5 (9 : Fin 32) = trp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_9]
    have g5_10 : reg n5 a0 = 0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
    have g5_21 : reg n5 (21 : Fin 32) = lp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = orp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
    have g5_23 : reg n5 (23 : Fin 32) = tcl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
    have g5_24 : reg n5 (24 : Fin 32) = sgl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
    have g5_25 : reg n5 (25 : Fin 32) = orl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = ll := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m5]; exact w4_78
    have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m5]; exact w4_7c
    have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m5]; exact w4_80
    have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m5]; exact w4_84
    have w5_a20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m5]; exact w4_a20
    clear w4_a20 w4_84 w4_80 w4_7c w4_78 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_19 g4_18 g4_10 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    exact .inl ⟨(fun ⟨tl2', h0', _⟩ => by rw [hr2] at h0'; cases h0'), sv_fail F E5 s5 t5 (fun x hx => (fR5 x hx).trans (fM x hx).symm) V5 hret g5_2 g5_18 hO g5_3 g5_4⟩
  obtain ⟨r2b, hr2b⟩ : ∃ r, derPosIntOf (memBytes M0 (rp) (rl).toNat) (rp) (.ok tl2) = r := ⟨_, rfl⟩
  rcases r2b with er2b | ⟨ip2, il2⟩
  · obtain ⟨zhr2b, -⟩ := Er2 er2b (by rw [hr2, hr2b])
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0xA20, 0x8), (0x180, 0x8)] := keep_kk1.trans K2
    clear keep_kk1
    have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K2.w32 (by decide) (by decide)).trans w1_78
    have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K2.w32 (by decide) (by decide)).trans w1_7c
    have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K2.w32 (by decide) (by decide)).trans w1_80
    have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K2.w32 (by decide) (by decide)).trans w1_84
    have w2_a20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := zhr2b
    clear w1_184 w1_180 w1_84 w1_80 w1_7c w1_78 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0x1DA: lw
    obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_1da (off' := 0x1DE) (by decide)
      (by rw [g2_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s3 : St n3.mem SV n3 0x1DE (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
    have g3_8 : reg n3 (8 : Fin 32) = trl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
    have g3_9 : reg n3 (9 : Fin 32) = trp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
    have g3_21 : reg n3 (21 : Fin 32) = lp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = orp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
    have g3_23 : reg n3 (23 : Fin 32) = tcl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
    have g3_24 : reg n3 (24 : Fin 32) = sgl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
    have g3_25 : reg n3 (25 : Fin 32) = orl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
    have g3_10 : reg n3 a0 = 0 := by
      rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g2_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w2_a20]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m3]; exact w2_78
    have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m3]; exact w2_7c
    have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m3]; exact w2_80
    have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m3]; exact w2_84
    have w3_a20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m3]; exact w2_a20
    clear w2_a20 w2_84 w2_80 w2_7c w2_78 zhr2b
    -- 0x1DE: branch, taken
    obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x962 sv_at_1de
      (by decide) (by rw [g3_10, s3.zero]; rfl)
    have s4 : St n4.mem SV n4 0x962 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
    have g4_8 : reg n4 (8 : Fin 32) = trl := by rw [u4.regs, g3_8]
    have g4_9 : reg n4 (9 : Fin 32) = trp := by rw [u4.regs, g3_9]
    have g4_10 : reg n4 a0 = 0 := by rw [u4.regs, g3_10]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
    have g4_21 : reg n4 (21 : Fin 32) = lp := by rw [u4.regs, g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = orp := by rw [u4.regs, g3_22]
    have g4_23 : reg n4 (23 : Fin 32) = tcl := by rw [u4.regs, g3_23]
    have g4_24 : reg n4 (24 : Fin 32) = sgl := by rw [u4.regs, g3_24]
    have g4_25 : reg n4 (25 : Fin 32) = orl := by rw [u4.regs, g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = ll := by rw [u4.regs, g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u4.regs, g3_27]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m4]; exact w3_78
    have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m4]; exact w3_7c
    have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m4]; exact w3_80
    have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m4]; exact w3_84
    have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m4]; exact w3_a20
    clear w3_a20 w3_84 w3_80 w3_7c w3_78 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_19 g3_18 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    -- 0x962: lbu
    obtain ⟨n5, d5, u5⟩ := s4.lbu E4.self sv_at_962 (off' := 0x966) (by decide)
    have s5 : St n5.mem SV n5 0x966 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
    have g5_8 : reg n5 (8 : Fin 32) = trl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_8]
    have g5_9 : reg n5 (9 : Fin 32) = trp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_9]
    have g5_10 : reg n5 a0 = 0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
    have g5_21 : reg n5 (21 : Fin 32) = lp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = orp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
    have g5_23 : reg n5 (23 : Fin 32) = tcl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
    have g5_24 : reg n5 (24 : Fin 32) = sgl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
    have g5_25 : reg n5 (25 : Fin 32) = orl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = ll := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m5]; exact w4_78
    have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m5]; exact w4_7c
    have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m5]; exact w4_80
    have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m5]; exact w4_84
    have w5_a20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m5]; exact w4_a20
    clear w4_a20 w4_84 w4_80 w4_7c w4_78 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_19 g4_18 g4_10 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    exact .inl ⟨(fun ⟨tl2', h0', ip2', il2', h1', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr2b] at h1'; cases h1'), sv_fail F E5 s5 t5 (fun x hx => (fR5 x hx).trans (fM x hx).symm) V5 hret g5_2 g5_18 hO g5_3 g5_4⟩
  obtain ⟨p0_2, p4_2⟩ := Ok2 ip2 il2 (by rw [hr2, hr2b])
  obtain ⟨d8_2, d12_2⟩ := A2 tl2 hr2
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0xA20, 0x8), (0x180, 0x8)] := keep_kk1.trans K2
  clear keep_kk1
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K2.w32 (by decide) (by decide)).trans w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K2.w32 (by decide) (by decide)).trans w1_7c
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K2.w32 (by decide) (by decide)).trans w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K2.w32 (by decide) (by decide)).trans w1_84
  have w2_180 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := d8_2
  have w2_184 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := d12_2
  have w2_a20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ip2 := p0_2
  have w2_a24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = il2 := p4_2
  clear w1_184 w1_180 w1_84 w1_80 w1_7c w1_78 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x1DA: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_1da (off' := 0x1DE) (by decide)
    (by rw [g2_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x1DE (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = trl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = trp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = lp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = orp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = tcl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = sgl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = orl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_10 : reg n3 a0 = ip2 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w2_a20]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m3]; exact w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m3]; exact w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m3]; exact w2_84
  have w3_180 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_180
  have w3_184 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_184
  have w3_a20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ip2 := by rw [m3]; exact w2_a20
  have w3_a24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = il2 := by rw [m3]; exact w2_a24
  clear w2_a24 w2_a20 w2_184 w2_180 w2_84 w2_80 w2_7c w2_78 d12_2 d8_2 p4_2 p0_2 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_19 g2_18 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 Er2 Ok2 A2 K2 rk2 sp2 s2 c2
  -- 0x1DE: branch, not taken
  obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0x1E2 sv_at_1de
    (by decide) (by rw [g3_10, s3.zero]; exact br_beq_f (tb_in.serial_ne hr2 hr2b))
  have s4 : St n4.mem SV n4 0x1E2 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = trl := by rw [u4.regs, g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = trp := by rw [u4.regs, g3_9]
  have g4_10 : reg n4 a0 = ip2 := by rw [u4.regs, g3_10]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = lp := by rw [u4.regs, g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = orp := by rw [u4.regs, g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = tcl := by rw [u4.regs, g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = sgl := by rw [u4.regs, g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = orl := by rw [u4.regs, g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = ll := by rw [u4.regs, g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u4.regs, g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m4]; exact w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m4]; exact w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m4]; exact w3_84
  have w4_180 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_180
  have w4_184 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_184
  have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ip2 := by rw [m4]; exact w3_a20
  have w4_a24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = il2 := by rw [m4]; exact w3_a24
  clear w3_a24 w3_a20 w3_184 w3_180 w3_84 w3_80 w3_7c w3_78 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_19 g3_18 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x1E2: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_1e2 (off' := 0x1E6) (by decide)
    (by rw [g4_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0x1E6 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = trl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = trp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = lp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = orp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = tcl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = sgl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = orl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = ll := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
  have g5_10 : reg n5 a0 = il2 := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, w4_a24]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m5]; exact w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m5]; exact w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m5]; exact w4_84
  have w5_180 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_180
  have w5_184 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_184
  have w5_a20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ip2 := by rw [m5]; exact w4_a20
  have w5_a24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = il2 := by rw [m5]; exact w4_a24
  clear w4_a24 w4_a20 w4_184 w4_180 w4_84 w4_80 w4_7c w4_78 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_19 g4_18 g4_10 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0x1E6
  obtain ⟨n6, c6, u6⟩ := s5.block svL31e6 E5.self svL31e6_end
    ⟨trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x1E8 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svL31e6 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_8 : reg n6 (8 : Fin 32) = trl := by
    rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = trp := by
    rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
  have g6_10 : reg n6 a0 = il2 := by
    rw [rb6, runBlock_reg _ _ _ a0 s5.zero (by decide), g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by
    rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = lp := by
    rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = orp := by
    rw [rb6, runBlock_reg _ _ _ (22 : Fin 32) s5.zero (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = tcl := by
    rw [rb6, runBlock_reg _ _ _ (23 : Fin 32) s5.zero (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = sgl := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = orl := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = ll := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_11 : reg n6 a1 = BitVec.ofNat 32 0x14 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svL31e6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_18, g5_19, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m6]; exact w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m6]; exact w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m6]; exact w5_84
  have w6_180 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_180
  have w6_184 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_184
  have w6_a20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ip2 := by rw [m6]; exact w5_a20
  have w6_a24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = il2 := by rw [m6]; exact w5_a24
  clear w5_a24 w5_a20 w5_184 w5_180 w5_84 w5_80 w5_7c w5_78 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  by_cases hz_6 : (il2).toNat ≤ 20
  rotate_left
  · -- 0x1E8: branch, taken
    obtain ⟨n7, d7, u7⟩ := s6.taken E6.self 0x966 sv_at_1e8
      (by decide) (by rw [g6_10, g6_11]; exact br_bltu_t (by rw [show (BitVec.ofNat 32 0x14).toNat = 20 from rfl]; omega))
    have s7 : St n7.mem SV n7 0x966 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
    have g7_8 : reg n7 (8 : Fin 32) = trl := by rw [u7.regs, g6_8]
    have g7_9 : reg n7 (9 : Fin 32) = trp := by rw [u7.regs, g6_9]
    have g7_10 : reg n7 a0 = il2 := by rw [u7.regs, g6_10]
    have g7_11 : reg n7 a1 = BitVec.ofNat 32 0x14 := by rw [u7.regs, g6_11]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
    have g7_21 : reg n7 (21 : Fin 32) = lp := by rw [u7.regs, g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = orp := by rw [u7.regs, g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = tcl := by rw [u7.regs, g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = sgl := by rw [u7.regs, g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = orl := by rw [u7.regs, g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = ll := by rw [u7.regs, g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u7.regs, g6_27]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m7]; exact w6_78
    have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m7]; exact w6_7c
    have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m7]; exact w6_80
    have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m7]; exact w6_84
    have w7_180 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_180
    have w7_184 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_184
    have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ip2 := by rw [m7]; exact w6_a20
    have w7_a24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = il2 := by rw [m7]; exact w6_a24
    clear w6_a24 w6_a20 w6_184 w6_180 w6_84 w6_80 w6_7c w6_78 g6_11 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
    exact .inl ⟨(fun ⟨tl2', h0', ip2', il2', h1', h2', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr2b] at h1'; cases h1'; exact hz_6 h2'), sv_fail F E7 s7 t7 (fun x hx => (fR7 x hx).trans (fM x hx).symm) V7 hret g7_2 g7_18 hO g7_3 g7_4⟩
  -- 0x1E8: branch, not taken
  obtain ⟨n7, d7, u7⟩ := s6.notTaken E6.self 0x1EC sv_at_1e8
    (by decide) (by rw [g6_10, g6_11]; exact br_bltu_f (by rw [show (BitVec.ofNat 32 0x14).toNat = 20 from rfl]; omega))
  have s7 : St n7.mem SV n7 0x1EC (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = trl := by rw [u7.regs, g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = trp := by rw [u7.regs, g6_9]
  have g7_10 : reg n7 a0 = il2 := by rw [u7.regs, g6_10]
  have g7_11 : reg n7 a1 = BitVec.ofNat 32 0x14 := by rw [u7.regs, g6_11]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = lp := by rw [u7.regs, g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = orp := by rw [u7.regs, g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = tcl := by rw [u7.regs, g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = sgl := by rw [u7.regs, g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = orl := by rw [u7.regs, g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = ll := by rw [u7.regs, g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u7.regs, g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m7]; exact w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m7]; exact w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m7]; exact w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m7]; exact w6_84
  have w7_180 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_180
  have w7_184 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_184
  have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ip2 := by rw [m7]; exact w6_a20
  have w7_a24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = il2 := by rw [m7]; exact w6_a24
  clear w6_a24 w6_a20 w6_184 w6_180 w6_84 w6_80 w6_7c w6_78 g6_11 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0x1EC
  obtain ⟨n8, c8, u8⟩ := s7.block svL31ec E7.self svL31ec_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x1FA (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svL31ec (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_8 : reg n8 (8 : Fin 32) = trl := by
    rw [rb8, runBlock_reg _ _ _ (8 : Fin 32) s7.zero (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = trp := by
    rw [rb8, runBlock_reg _ _ _ (9 : Fin 32) s7.zero (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = lp := by
    rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = orp := by
    rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = tcl := by
    rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = sgl := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = orl := by
    rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = ll := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svL31ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_11, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_11 : reg n8 a1 = B + 0x21A0 + BitVec.ofNat 32 0x178 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svL31ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_11, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_12 : reg n8 a2 = BitVec.ofNat 32 0x30 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svL31ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_11, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0xA20, 0x8), (0x180, 0x8)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m8]; exact w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m8]; exact w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m8]; exact w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m8]; exact w7_84
  have w8_180 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_180
  have w8_184 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_184
  have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ip2 := by rw [m8]; exact w7_a20
  have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = il2 := by rw [m8]; exact w7_a24
  clear w7_a24 w7_a20 w7_184 w7_180 w7_84 w7_80 w7_7c w7_78 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_11 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x1FA: sv_elemF
  obtain ⟨n9, c9, s9, rk9, K9, Ok9, Er9, fr9⟩ := sv_elemF (oc := 0xA20) (dc := 0x178) (tag := 0x30)
    F E8 s8 sv_at_1fa sv_at_1fe (by decide) (by decide) g8_10 g8_11 g8_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w8_180 w8_184
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keepL K9 (by decide)
  rw [sv_mb fR8 (tb_in.restW hr2)] at Ok9 Er9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rk9 sp (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk9 (3 : Fin 32) (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk9 (4 : Fin 32) (by decide) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = trl := by rw [rk9 (8 : Fin 32) (by decide) (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = trp := by rw [rk9 (9 : Fin 32) (by decide) (by decide), g8_9]
  have g9_10 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk9 a0 (by decide) (by decide), g8_10]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rk9 (18 : Fin 32) (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rk9 (19 : Fin 32) (by decide) (by decide), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = lp := by rw [rk9 (21 : Fin 32) (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = orp := by rw [rk9 (22 : Fin 32) (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = tcl := by rw [rk9 (23 : Fin 32) (by decide) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = sgl := by rw [rk9 (24 : Fin 32) (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = orl := by rw [rk9 (25 : Fin 32) (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = ll := by rw [rk9 (26 : Fin 32) (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk9 (27 : Fin 32) (by decide) (by decide), g8_27]
  obtain ⟨r9, hr9⟩ : ∃ r, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = r := ⟨_, rfl⟩
  rcases r9 with er9 | tl9
  · obtain ⟨zhr9, -⟩ := Er9 er9 hr9
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8)] := keep_kk8.trans K9
    clear keep_kk8
    have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K9.w32 (by decide) (by decide)).trans w8_78
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K9.w32 (by decide) (by decide)).trans w8_7c
    have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K9.w32 (by decide) (by decide)).trans w8_80
    have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K9.w32 (by decide) (by decide)).trans w8_84
    have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := zhr9
    clear w8_a24 w8_a20 w8_184 w8_180 w8_84 w8_80 w8_7c w8_78 g8_12 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
    -- 0x202: lw
    obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_202 (off' := 0x206) (by decide)
      (by rw [g9_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s10 : St n10.mem SV n10 0x206 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = trl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = trp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_9]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
    have g10_21 : reg n10 (21 : Fin 32) = lp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = orp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = tcl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = sgl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = orl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = ll := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
    have g10_10 : reg n10 a0 = 0 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g9_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w9_a20]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m10]; exact w9_78
    have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m10]; exact w9_7c
    have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m10]; exact w9_80
    have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m10]; exact w9_84
    have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m10]; exact w9_a20
    clear w9_a20 w9_84 w9_80 w9_7c w9_78 zhr9
    -- 0x206: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x962 sv_at_206
      (by decide) (by rw [g10_10, s10.zero]; rfl)
    have s11 : St n11.mem SV n11 0x962 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = trl := by rw [u11.regs, g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = trp := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = 0 := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_21 : reg n11 (21 : Fin 32) = lp := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = orp := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = tcl := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = sgl := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = orl := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = ll := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m11]; exact w10_78
    have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m11]; exact w10_7c
    have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m11]; exact w10_80
    have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m11]; exact w10_84
    have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m11]; exact w10_a20
    clear w10_a20 w10_84 w10_80 w10_7c w10_78 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x962: lbu
    obtain ⟨n12, d12, u12⟩ := s11.lbu E11.self sv_at_962 (off' := 0x966) (by decide)
    have s12 : St n12.mem SV n12 0x966 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
    have g12_8 : reg n12 (8 : Fin 32) = trl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
    have g12_9 : reg n12 (9 : Fin 32) = trp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
    have g12_10 : reg n12 a0 = 0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_10]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
    have g12_21 : reg n12 (21 : Fin 32) = lp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = orp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = tcl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = sgl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = orl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = ll := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m12]; exact w11_78
    have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m12]; exact w11_7c
    have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m12]; exact w11_80
    have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m12]; exact w11_84
    have w12_a20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m12]; exact w11_a20
    clear w11_a20 w11_84 w11_80 w11_7c w11_78 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    exact .inl ⟨(fun ⟨tl2', h0', ip2', il2', h1', h2', tl9', h3', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr2b] at h1'; cases h1'; rw [hr9] at h3'; cases h3'), sv_fail F E12 s12 t12 (fun x hx => (fR12 x hx).trans (fM x hx).symm) V12 hret g12_2 g12_18 hO g12_3 g12_4⟩
  obtain ⟨o0_9, o4_9, o8_9, o12_9, o16_9, d8_9, d12_9⟩ := Ok9 tl9 hr9
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8)] := keep_kk8.trans K9
  clear keep_kk8
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K9.w32 (by decide) (by decide)).trans w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K9.w32 (by decide) (by decide)).trans w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K9.w32 (by decide) (by decide)).trans w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K9.w32 (by decide) (by decide)).trans w8_84
  have w9_180 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := d8_9
  have w9_184 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := d12_9
  have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := o0_9
  have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl9.len := o4_9
  have w9_a28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := o8_9
  have w9_a2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl9.header + tl9.len) := o12_9
  have b9_a30 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl9.tag := o16_9
  clear w8_a24 w8_a20 w8_184 w8_180 w8_84 w8_80 w8_7c w8_78 g8_12 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0x202: lw
  obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_202 (off' := 0x206) (by decide)
    (by rw [g9_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s10 : St n10.mem SV n10 0x206 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = trl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = trp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = lp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = orp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = tcl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = sgl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = orl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = ll := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
  have g10_10 : reg n10 a0 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w9_a20]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m10]; exact w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m10]; exact w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m10]; exact w9_84
  have w10_180 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m10]; exact w9_180
  have w10_184 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m10]; exact w9_184
  have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [m10]; exact w9_a20
  have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl9.len := by rw [m10]; exact w9_a24
  have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_a28
  have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m10]; exact w9_a2c
  have b10_a30 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl9.tag := by rw [m10]; exact b9_a30
  clear b9_a30 w9_a2c w9_a28 w9_a24 w9_a20 w9_184 w9_180 w9_84 w9_80 w9_7c w9_78 d12_9 d8_9 o16_9 o12_9 o8_9 o4_9 o0_9 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 Er9 Ok9 K9 rk9 s9 c9
  -- 0x206: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0x20A sv_at_206
    (by decide) (by rw [g10_10, s10.zero]; exact br_beq_f ((tb_in.restW hr2).ok_ne hr9))
  have s11 : St n11.mem SV n11 0x20A (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = trl := by rw [u11.regs, g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = trp := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [u11.regs, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = lp := by rw [u11.regs, g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = orp := by rw [u11.regs, g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = tcl := by rw [u11.regs, g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = sgl := by rw [u11.regs, g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = orl := by rw [u11.regs, g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = ll := by rw [u11.regs, g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m11]; exact w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m11]; exact w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m11]; exact w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m11]; exact w10_84
  have w11_180 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m11]; exact w10_180
  have w11_184 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m11]; exact w10_184
  have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [m11]; exact w10_a20
  have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl9.len := by rw [m11]; exact w10_a24
  have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_a28
  have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m11]; exact w10_a2c
  have b11_a30 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl9.tag := by rw [m11]; exact b10_a30
  clear b10_a30 w10_a2c w10_a28 w10_a24 w10_a20 w10_184 w10_180 w10_84 w10_80 w10_7c w10_78 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x20A: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_20a (off' := 0x20E) (by decide)
    (by rw [g11_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x20E (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = trl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = trp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
  have g12_10 : reg n12 a0 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [u12.regs, upd_ne (by decide) (by decide), g11_10]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = lp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = orp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_24 : reg n12 (24 : Fin 32) = sgl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = orl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = ll := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_23 : reg n12 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr, w11_a28]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m12]; exact w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m12]; exact w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m12]; exact w11_84
  have w12_180 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m12]; exact w11_180
  have w12_184 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m12]; exact w11_184
  have w12_a20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [m12]; exact w11_a20
  have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl9.len := by rw [m12]; exact w11_a24
  have w12_a28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_a28
  have w12_a2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m12]; exact w11_a2c
  have b12_a30 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl9.tag := by rw [m12]; exact b11_a30
  clear b11_a30 w11_a2c w11_a28 w11_a24 w11_a20 w11_184 w11_180 w11_84 w11_80 w11_7c w11_78 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x20E: lw
  obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_20e (off' := 0x212) (by decide)
    (by rw [g12_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s13 : St n13.mem SV n13 0x212 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_9 : reg n13 (9 : Fin 32) = trp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_9]
  have g13_10 : reg n13 a0 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [u13.regs, upd_ne (by decide) (by decide), g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = lp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = orp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = sgl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = orl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = ll := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr, w12_a2c]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m13]; exact w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m13]; exact w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m13]; exact w12_84
  have w13_180 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m13]; exact w12_180
  have w13_184 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m13]; exact w12_184
  have w13_a20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [m13]; exact w12_a20
  have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl9.len := by rw [m13]; exact w12_a24
  have w13_a28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m13]; exact w12_a28
  have w13_a2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m13]; exact w12_a2c
  have b13_a30 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl9.tag := by rw [m13]; exact b12_a30
  clear b12_a30 w12_a2c w12_a28 w12_a24 w12_a20 w12_184 w12_180 w12_84 w12_80 w12_7c w12_78 g12_23 g12_27 g12_26 g12_25 g12_24 g12_22 g12_21 g12_19 g12_18 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x212: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_212 (off' := 0x216) (c := 0x1020)
    (by decide) (by rw [g13_27]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [rg14 (8 : Fin 32), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = trp := by rw [rg14 (9 : Fin 32), g13_9]
  have g14_10 : reg n14 a0 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [rg14 a0, g13_10]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_21 : reg n14 (21 : Fin 32) = lp := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = orp := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg14 (23 : Fin 32), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = sgl := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = orl := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = ll := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K14.w32 (by decide) (by decide)).trans w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K14.w32 (by decide) (by decide)).trans w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K14.w32 (by decide) (by decide)).trans w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K14.w32 (by decide) (by decide)).trans w13_84
  have w14_180 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K14.w32 (by decide) (by decide)).trans w13_180
  have w14_184 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K14.w32 (by decide) (by decide)).trans w13_184
  have w14_a20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := (K14.w32 (by decide) (by decide)).trans w13_a20
  have w14_a24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl9.len := (K14.w32 (by decide) (by decide)).trans w13_a24
  have w14_a28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K14.w32 (by decide) (by decide)).trans w13_a28
  have w14_a2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K14.w32 (by decide) (by decide)).trans w13_a2c
  have b14_a30 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl9.tag := (K14.b8 (by decide) (by decide)).trans b13_a30
  have w14_1020 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [W14, g13_23]
  clear b13_a30 w13_a2c w13_a28 w13_a24 w13_a20 w13_184 w13_180 w13_84 w13_80 w13_7c w13_78 g13_8 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_19 g13_18 g13_10 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0x216: sw
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sw F E14 s14 sv_at_216 (off' := 0x21A) (c := 0x1024)
    (by decide) (by rw [g14_27]; sv_addr) (by decide) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [rg15 (8 : Fin 32), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = trp := by rw [rg15 (9 : Fin 32), g14_9]
  have g15_10 : reg n15 a0 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [rg15 a0, g14_10]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rg15 (18 : Fin 32), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rg15 (19 : Fin 32), g14_19]
  have g15_21 : reg n15 (21 : Fin 32) = lp := by rw [rg15 (21 : Fin 32), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = orp := by rw [rg15 (22 : Fin 32), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg15 (23 : Fin 32), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = sgl := by rw [rg15 (24 : Fin 32), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = orl := by rw [rg15 (25 : Fin 32), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = ll := by rw [rg15 (26 : Fin 32), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg15 (27 : Fin 32), g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K15.w32 (by decide) (by decide)).trans w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K15.w32 (by decide) (by decide)).trans w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K15.w32 (by decide) (by decide)).trans w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K15.w32 (by decide) (by decide)).trans w14_84
  have w15_180 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K15.w32 (by decide) (by decide)).trans w14_180
  have w15_184 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K15.w32 (by decide) (by decide)).trans w14_184
  have w15_a20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := (K15.w32 (by decide) (by decide)).trans w14_a20
  have w15_a24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl9.len := (K15.w32 (by decide) (by decide)).trans w14_a24
  have w15_a28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K15.w32 (by decide) (by decide)).trans w14_a28
  have w15_a2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K15.w32 (by decide) (by decide)).trans w14_a2c
  have w15_1020 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K15.w32 (by decide) (by decide)).trans w14_1020
  have b15_a30 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl9.tag := (K15.b8 (by decide) (by decide)).trans b14_a30
  have w15_1024 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [W15, g14_8]
  clear w14_1020 b14_a30 w14_a2c w14_a28 w14_a24 w14_a20 w14_184 w14_180 w14_84 w14_80 w14_7c w14_78 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_19 g14_18 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0x21A: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_21a (off' := 0x21E) (c := 0x1028)
    (by decide) (by rw [g15_27]; sv_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [rg16 (8 : Fin 32), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = trp := by rw [rg16 (9 : Fin 32), g15_9]
  have g16_10 : reg n16 a0 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [rg16 a0, g15_10]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_21 : reg n16 (21 : Fin 32) = lp := by rw [rg16 (21 : Fin 32), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = orp := by rw [rg16 (22 : Fin 32), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg16 (23 : Fin 32), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = sgl := by rw [rg16 (24 : Fin 32), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = orl := by rw [rg16 (25 : Fin 32), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = ll := by rw [rg16 (26 : Fin 32), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg16 (27 : Fin 32), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K16.w32 (by decide) (by decide)).trans w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K16.w32 (by decide) (by decide)).trans w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K16.w32 (by decide) (by decide)).trans w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K16.w32 (by decide) (by decide)).trans w15_84
  have w16_180 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K16.w32 (by decide) (by decide)).trans w15_180
  have w16_184 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K16.w32 (by decide) (by decide)).trans w15_184
  have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := (K16.w32 (by decide) (by decide)).trans w15_a20
  have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl9.len := (K16.w32 (by decide) (by decide)).trans w15_a24
  have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K16.w32 (by decide) (by decide)).trans w15_a28
  have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K16.w32 (by decide) (by decide)).trans w15_a2c
  have w16_1020 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K16.w32 (by decide) (by decide)).trans w15_1020
  have w16_1024 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K16.w32 (by decide) (by decide)).trans w15_1024
  have b16_a30 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl9.tag := (K16.b8 (by decide) (by decide)).trans b15_a30
  have w16_1028 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [W16, g15_23]
  clear w15_1024 b15_a30 w15_1020 w15_a2c w15_a28 w15_a24 w15_a20 w15_184 w15_180 w15_84 w15_80 w15_7c w15_78 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  -- 0x21E: sw
  obtain ⟨n17, d17, s17, fr17, K17, W17, rg17⟩ := sv_sw F E16 s16 sv_at_21e (off' := 0x222) (c := 0x102C)
    (by decide) (by rw [g16_27]; sv_addr) (by decide) (by decide)
  have t17 : Steps n0 n17 := t16.trans d17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rg17 sp, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg17 (3 : Fin 32), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg17 (4 : Fin 32), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [rg17 (8 : Fin 32), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = trp := by rw [rg17 (9 : Fin 32), g16_9]
  have g17_10 : reg n17 a0 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [rg17 a0, g16_10]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [rg17 (18 : Fin 32), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [rg17 (19 : Fin 32), g16_19]
  have g17_21 : reg n17 (21 : Fin 32) = lp := by rw [rg17 (21 : Fin 32), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = orp := by rw [rg17 (22 : Fin 32), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg17 (23 : Fin 32), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = sgl := by rw [rg17 (24 : Fin 32), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = orl := by rw [rg17 (25 : Fin 32), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = ll := by rw [rg17 (26 : Fin 32), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg17 (27 : Fin 32), g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K17.w32 (by decide) (by decide)).trans w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K17.w32 (by decide) (by decide)).trans w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K17.w32 (by decide) (by decide)).trans w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K17.w32 (by decide) (by decide)).trans w16_84
  have w17_180 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K17.w32 (by decide) (by decide)).trans w16_180
  have w17_184 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K17.w32 (by decide) (by decide)).trans w16_184
  have w17_a20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := (K17.w32 (by decide) (by decide)).trans w16_a20
  have w17_a24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl9.len := (K17.w32 (by decide) (by decide)).trans w16_a24
  have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K17.w32 (by decide) (by decide)).trans w16_a28
  have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K17.w32 (by decide) (by decide)).trans w16_a2c
  have w17_1020 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K17.w32 (by decide) (by decide)).trans w16_1020
  have w17_1024 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K17.w32 (by decide) (by decide)).trans w16_1024
  have w17_1028 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K17.w32 (by decide) (by decide)).trans w16_1028
  have b17_a30 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl9.tag := (K17.b8 (by decide) (by decide)).trans b16_a30
  have w17_102c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [W17, g16_8]
  clear w16_1028 b16_a30 w16_1024 w16_1020 w16_a2c w16_a28 w16_a24 w16_a20 w16_184 w16_180 w16_84 w16_80 w16_7c w16_78 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_19 g16_18 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0x222
  obtain ⟨n18, c18, u18⟩ := s17.block svL3222 E17.self svL3222_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem SV n18 0x232 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock svL3222 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans c18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by
    rw [rb18, runBlock_reg _ _ _ sp s17.zero (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (3 : Fin 32) s17.zero (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (4 : Fin 32) s17.zero (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by
    rw [rb18, runBlock_reg _ _ _ (8 : Fin 32) s17.zero (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = trp := by
    rw [rb18, runBlock_reg _ _ _ (9 : Fin 32) s17.zero (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by
    rw [rb18, runBlock_reg _ _ _ (18 : Fin 32) s17.zero (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by
    rw [rb18, runBlock_reg _ _ _ (19 : Fin 32) s17.zero (by decide), g17_19]
  have g18_21 : reg n18 (21 : Fin 32) = lp := by
    rw [rb18, runBlock_reg _ _ _ (21 : Fin 32) s17.zero (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = orp := by
    rw [rb18, runBlock_reg _ _ _ (22 : Fin 32) s17.zero (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [rb18, runBlock_reg _ _ _ (23 : Fin 32) s17.zero (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = sgl := by
    rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = orl := by
    rw [rb18, runBlock_reg _ _ _ (25 : Fin 32) s17.zero (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = ll := by
    rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb18, runBlock_reg _ _ _ (27 : Fin 32) s17.zero (by decide), g17_27]
  have g18_10 : reg n18 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svL3222, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_10, g17_18, g17_19, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_11 : reg n18 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svL3222, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_10, g17_18, g17_19, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m18]; exact w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m18]; exact w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m18]; exact w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m18]; exact w17_84
  have w18_180 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_180
  have w18_184 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_184
  have w18_a20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl9.header := by rw [m18]; exact w17_a20
  have w18_a24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl9.len := by rw [m18]; exact w17_a24
  have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m18]; exact w17_a28
  have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_a2c
  have w18_1020 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m18]; exact w17_1020
  have w18_1024 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_1024
  have w18_1028 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m18]; exact w17_1028
  have w18_102c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_102c
  have b18_a30 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl9.tag := by rw [m18]; exact b17_a30
  clear w17_102c b17_a30 w17_1028 w17_1024 w17_1020 w17_a2c w17_a28 w17_a24 w17_a20 w17_184 w17_180 w17_84 w17_80 w17_7c w17_78 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_19 g17_18 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
  -- 0x232: sv_algF
  obtain ⟨n19, c19, s19, sp19, rk19, K19, A19, R19, fr19⟩ := sv_algF (oc := 0xA20) (dc := 0x1020) (nl := tl9.header + tl9.len)
    F E18 s18 sv_at_232 sv_at_236 (by decide) (by decide) g18_2 g18_10 g18_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w18_1028 w18_102c ((tb_in.restW hr2).rawN hr9)
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keepL K19 (by decide)
  rw [derAlgOf_congr (sv_pt fR18 ((tb_in.restW hr2).rawN hr9))] at R19
  rw [sv_mb fR18 ((tb_in.restW hr2).rawN hr9)] at A19
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk19 (3 : Fin 32) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk19 (4 : Fin 32) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [rk19 (8 : Fin 32) (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = trp := by rw [rk19 (9 : Fin 32) (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rk19 (18 : Fin 32) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rk19 (19 : Fin 32) (by decide), g18_19]
  have g19_21 : reg n19 (21 : Fin 32) = lp := by rw [rk19 (21 : Fin 32) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = orp := by rw [rk19 (22 : Fin 32) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rk19 (23 : Fin 32) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = sgl := by rw [rk19 (24 : Fin 32) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = orl := by rw [rk19 (25 : Fin 32) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = ll := by rw [rk19 (26 : Fin 32) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk19 (27 : Fin 32) (by decide), g18_27]
  have g19_2 : reg n19 sp = B + 0x21A0 := sp19
  obtain ⟨r19, hr19⟩ : ∃ r, derAlgOf M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) (tl9.header + tl9.len) = r := ⟨_, rfl⟩
  rcases r19 with ab19 | ⟨⟨op19, ol19⟩, _ | ⟨prp19, pu19⟩⟩
  · rw [hr19] at R19
    obtain ⟨y0_19, -⟩ := R19
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8)] := keep_kk18.trans K19
    clear keep_kk18
    have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K19.w32 (by decide) (by decide)).trans w18_78
    have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K19.w32 (by decide) (by decide)).trans w18_7c
    have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K19.w32 (by decide) (by decide)).trans w18_80
    have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K19.w32 (by decide) (by decide)).trans w18_84
    have w19_180 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_180
    have w19_184 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_184
    have w19_1020 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K19.w32 (by decide) (by decide)).trans w18_1020
    have w19_1024 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_1024
    have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := y0_19
    clear b18_a30 w18_102c w18_1028 w18_1024 w18_1020 w18_a2c w18_a28 w18_a24 w18_a20 w18_184 w18_180 w18_84 w18_80 w18_7c w18_78 g18_11 g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
    -- 0x23A: lw
    obtain ⟨n20, d20, u20⟩ := s19.lw E19.self sv_at_23a (off' := 0x23E) (by decide)
      (by rw [g19_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s20 : St n20.mem SV n20 0x23E (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
    have t20 : Steps n0 n20 := t19.trans (.single d20)
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.same m20
    have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_4]
    have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_8]
    have g20_9 : reg n20 (9 : Fin 32) = trp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_9]
    have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, upd_ne (by decide) (by decide), g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_19]
    have g20_21 : reg n20 (21 : Fin 32) = lp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = orp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = sgl := by rw [u20.regs, upd_ne (by decide) (by decide), g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = orl := by rw [u20.regs, upd_ne (by decide) (by decide), g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = ll := by rw [u20.regs, upd_ne (by decide) (by decide), g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_27]
    have g20_10 : reg n20 a0 = 0 := by
      rw [u20.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g19_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w19_a20]
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m20]; exact w19_78
    have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m20]; exact w19_7c
    have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m20]; exact w19_80
    have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m20]; exact w19_84
    have w20_180 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m20]; exact w19_180
    have w20_184 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m20]; exact w19_184
    have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m20]; exact w19_a20
    have w20_1020 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_1020
    have w20_1024 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m20]; exact w19_1024
    clear w19_a20 w19_1024 w19_1020 w19_184 w19_180 w19_84 w19_80 w19_7c w19_78 y0_19
    -- 0x23E: branch, taken
    obtain ⟨n21, d21, u21⟩ := s20.taken E20.self 0x962 sv_at_23e
      (by decide) (by rw [g20_10, s20.zero]; rfl)
    have s21 : St n21.mem SV n21 0x962 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
    have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u21.regs, g20_8]
    have g21_9 : reg n21 (9 : Fin 32) = trp := by rw [u21.regs, g20_9]
    have g21_10 : reg n21 a0 = 0 := by rw [u21.regs, g20_10]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, g20_19]
    have g21_21 : reg n21 (21 : Fin 32) = lp := by rw [u21.regs, g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = orp := by rw [u21.regs, g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u21.regs, g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = sgl := by rw [u21.regs, g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = orl := by rw [u21.regs, g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = ll := by rw [u21.regs, g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u21.regs, g20_27]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m21]; exact w20_78
    have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m21]; exact w20_7c
    have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m21]; exact w20_80
    have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m21]; exact w20_84
    have w21_180 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_180
    have w21_184 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_184
    have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m21]; exact w20_a20
    have w21_1020 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_1020
    have w21_1024 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_1024
    clear w20_1024 w20_1020 w20_a20 w20_184 w20_180 w20_84 w20_80 w20_7c w20_78 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
    -- 0x962: lbu
    obtain ⟨n22, d22, u22⟩ := s21.lbu E21.self sv_at_962 (off' := 0x966) (by decide)
    have s22 : St n22.mem SV n22 0x966 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = trp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
    have g22_10 : reg n22 a0 = 0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_10]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
    have g22_21 : reg n22 (21 : Fin 32) = lp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = orp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = sgl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = orl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = ll := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m22]; exact w21_78
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m22]; exact w21_7c
    have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m22]; exact w21_80
    have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m22]; exact w21_84
    have w22_180 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_180
    have w22_184 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_184
    have w22_a20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m22]; exact w21_a20
    have w22_1020 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m22]; exact w21_1020
    have w22_1024 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_1024
    clear w21_1024 w21_1020 w21_a20 w21_184 w21_180 w21_84 w21_80 w21_7c w21_78 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_19 g21_18 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
    exact .inl ⟨(fun ⟨tl2', h0', ip2', il2', h1', h2', tl9', h3', op19', ol19', h4', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr2b] at h1'; cases h1'; rw [hr9] at h3'; cases h3'; rw [hr19] at h4'; cases h4'), sv_fail F E22 s22 t22 (fun x hx => (fR22 x hx).trans (fM x hx).symm) V22 hret g22_2 g22_18 hO g22_3 g22_4⟩
  rotate_left
  · rw [hr19] at R19
    obtain ⟨y0_19, y4_19, y8_19, -, -⟩ := R19
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8)] := keep_kk18.trans K19
    clear keep_kk18
    have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K19.w32 (by decide) (by decide)).trans w18_78
    have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K19.w32 (by decide) (by decide)).trans w18_7c
    have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K19.w32 (by decide) (by decide)).trans w18_80
    have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K19.w32 (by decide) (by decide)).trans w18_84
    have w19_180 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_180
    have w19_184 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_184
    have w19_1020 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K19.w32 (by decide) (by decide)).trans w18_1020
    have w19_1024 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_1024
    have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := y0_19
    have w19_a24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := y4_19
    have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := y8_19
    clear b18_a30 w18_102c w18_1028 w18_1024 w18_1020 w18_a2c w18_a28 w18_a24 w18_a20 w18_184 w18_180 w18_84 w18_80 w18_7c w18_78 g18_11 g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
    -- 0x23A: lw
    obtain ⟨n20, d20, u20⟩ := s19.lw E19.self sv_at_23a (off' := 0x23E) (by decide)
      (by rw [g19_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s20 : St n20.mem SV n20 0x23E (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
    have t20 : Steps n0 n20 := t19.trans (.single d20)
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.same m20
    have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_4]
    have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_8]
    have g20_9 : reg n20 (9 : Fin 32) = trp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_9]
    have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, upd_ne (by decide) (by decide), g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_19]
    have g20_21 : reg n20 (21 : Fin 32) = lp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = orp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = sgl := by rw [u20.regs, upd_ne (by decide) (by decide), g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = orl := by rw [u20.regs, upd_ne (by decide) (by decide), g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = ll := by rw [u20.regs, upd_ne (by decide) (by decide), g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_27]
    have g20_10 : reg n20 a0 = op19 := by
      rw [u20.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g19_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w19_a20]
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m20]; exact w19_78
    have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m20]; exact w19_7c
    have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m20]; exact w19_80
    have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m20]; exact w19_84
    have w20_180 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m20]; exact w19_180
    have w20_184 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m20]; exact w19_184
    have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m20]; exact w19_a20
    have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m20]; exact w19_a24
    have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := by rw [m20]; exact w19_a28
    have w20_1020 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_1020
    have w20_1024 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m20]; exact w19_1024
    clear w19_a28 w19_a24 w19_a20 w19_1024 w19_1020 w19_184 w19_180 w19_84 w19_80 w19_7c w19_78 y8_19 y4_19 y0_19
    -- 0x23E: branch, not taken
    obtain ⟨n21, d21, u21⟩ := s20.notTaken E20.self 0x242 sv_at_23e
      (by decide) (by rw [g20_10, s20.zero]; exact br_beq_f (((tb_in.restW hr2).rawN hr9).algOid hr19).pos_ne)
    have s21 : St n21.mem SV n21 0x242 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
    have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u21.regs, g20_8]
    have g21_9 : reg n21 (9 : Fin 32) = trp := by rw [u21.regs, g20_9]
    have g21_10 : reg n21 a0 = op19 := by rw [u21.regs, g20_10]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, g20_19]
    have g21_21 : reg n21 (21 : Fin 32) = lp := by rw [u21.regs, g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = orp := by rw [u21.regs, g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u21.regs, g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = sgl := by rw [u21.regs, g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = orl := by rw [u21.regs, g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = ll := by rw [u21.regs, g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u21.regs, g20_27]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m21]; exact w20_78
    have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m21]; exact w20_7c
    have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m21]; exact w20_80
    have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m21]; exact w20_84
    have w21_180 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_180
    have w21_184 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_184
    have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m21]; exact w20_a20
    have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m21]; exact w20_a24
    have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := by rw [m21]; exact w20_a28
    have w21_1020 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_1020
    have w21_1024 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_1024
    clear w20_1024 w20_1020 w20_a28 w20_a24 w20_a20 w20_184 w20_180 w20_84 w20_80 w20_7c w20_78 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
    -- 0x242: sw
    obtain ⟨n22, d22, s22, fr22, K22, W22, rg22⟩ := sv_sw F E21 s21 sv_at_242 (off' := 0x244) (c := 0x74)
      (by decide) (by rw [g21_2]; sv_addr) (by decide) (by decide)
    have t22 : Steps n0 n22 := t21.trans d22
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.keep K22 (by decide)
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [rg22 sp, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg22 (3 : Fin 32), g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg22 (4 : Fin 32), g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [rg22 (8 : Fin 32), g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = trp := by rw [rg22 (9 : Fin 32), g21_9]
    have g22_10 : reg n22 a0 = op19 := by rw [rg22 a0, g21_10]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rg22 (18 : Fin 32), g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rg22 (19 : Fin 32), g21_19]
    have g22_21 : reg n22 (21 : Fin 32) = lp := by rw [rg22 (21 : Fin 32), g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = orp := by rw [rg22 (22 : Fin 32), g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg22 (23 : Fin 32), g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = sgl := by rw [rg22 (24 : Fin 32), g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = orl := by rw [rg22 (25 : Fin 32), g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = ll := by rw [rg22 (26 : Fin 32), g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg22 (27 : Fin 32), g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4)] := keep_kk21.trans K22.toL
    clear keep_kk21
    have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K22.w32 (by decide) (by decide)).trans w21_78
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K22.w32 (by decide) (by decide)).trans w21_7c
    have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K22.w32 (by decide) (by decide)).trans w21_80
    have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K22.w32 (by decide) (by decide)).trans w21_84
    have w22_180 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K22.w32 (by decide) (by decide)).trans w21_180
    have w22_184 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K22.w32 (by decide) (by decide)).trans w21_184
    have w22_a20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := (K22.w32 (by decide) (by decide)).trans w21_a20
    have w22_a24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := (K22.w32 (by decide) (by decide)).trans w21_a24
    have w22_a28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := (K22.w32 (by decide) (by decide)).trans w21_a28
    have w22_1020 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K22.w32 (by decide) (by decide)).trans w21_1020
    have w22_1024 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K22.w32 (by decide) (by decide)).trans w21_1024
    have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [W22, g21_8]
    clear w21_1024 w21_1020 w21_a28 w21_a24 w21_a20 w21_184 w21_180 w21_84 w21_80 w21_7c w21_78 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_19 g21_18 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
    -- 0x244: sw
    obtain ⟨n23, d23, s23, fr23, K23, W23, rg23⟩ := sv_sw F E22 s22 sv_at_244 (off' := 0x246) (c := 0x70)
      (by decide) (by rw [g22_2]; sv_addr) (by decide) (by decide)
    have t23 : Steps n0 n23 := t22.trans d23
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.keep K23 (by decide)
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [rg23 sp, g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg23 (3 : Fin 32), g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg23 (4 : Fin 32), g22_4]
    have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [rg23 (8 : Fin 32), g22_8]
    have g23_9 : reg n23 (9 : Fin 32) = trp := by rw [rg23 (9 : Fin 32), g22_9]
    have g23_10 : reg n23 a0 = op19 := by rw [rg23 a0, g22_10]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [rg23 (18 : Fin 32), g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [rg23 (19 : Fin 32), g22_19]
    have g23_21 : reg n23 (21 : Fin 32) = lp := by rw [rg23 (21 : Fin 32), g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = orp := by rw [rg23 (22 : Fin 32), g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg23 (23 : Fin 32), g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = sgl := by rw [rg23 (24 : Fin 32), g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = orl := by rw [rg23 (25 : Fin 32), g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = ll := by rw [rg23 (26 : Fin 32), g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg23 (27 : Fin 32), g22_27]
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := keep_kk22.trans K23.toL
    clear keep_kk22
    have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K23.w32 (by decide) (by decide)).trans w22_74
    have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K23.w32 (by decide) (by decide)).trans w22_78
    have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K23.w32 (by decide) (by decide)).trans w22_7c
    have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K23.w32 (by decide) (by decide)).trans w22_80
    have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K23.w32 (by decide) (by decide)).trans w22_84
    have w23_180 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K23.w32 (by decide) (by decide)).trans w22_180
    have w23_184 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K23.w32 (by decide) (by decide)).trans w22_184
    have w23_a20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := (K23.w32 (by decide) (by decide)).trans w22_a20
    have w23_a24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := (K23.w32 (by decide) (by decide)).trans w22_a24
    have w23_a28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := (K23.w32 (by decide) (by decide)).trans w22_a28
    have w23_1020 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K23.w32 (by decide) (by decide)).trans w22_1020
    have w23_1024 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K23.w32 (by decide) (by decide)).trans w22_1024
    have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [W23, g22_23]
    clear w22_74 w22_1024 w22_1020 w22_a28 w22_a24 w22_a20 w22_184 w22_180 w22_84 w22_80 w22_7c w22_78 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_19 g22_18 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 rg22 W22 K22 fr22 s22 d22
    -- 0x246
    obtain ⟨n24, c24, u24⟩ := s23.block svL3246 E23.self svL3246_end
      ⟨trivial, trivial⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have s24 : St n24.mem SV n24 0x248 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have rb24 : ∀ q, reg n24 q = (runBlock svL3246 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans c24
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by
      rw [rb24, runBlock_reg _ _ _ sp s23.zero (by decide), g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb24, runBlock_reg _ _ _ (3 : Fin 32) s23.zero (by decide), g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb24, runBlock_reg _ _ _ (4 : Fin 32) s23.zero (by decide), g23_4]
    have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by
      rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
    have g24_9 : reg n24 (9 : Fin 32) = trp := by
      rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
    have g24_10 : reg n24 a0 = op19 := by
      rw [rb24, runBlock_reg _ _ _ a0 s23.zero (by decide), g23_10]
    have g24_18 : reg n24 (18 : Fin 32) = out := by
      rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by
      rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
    have g24_21 : reg n24 (21 : Fin 32) = lp := by
      rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = orp := by
      rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by
      rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = sgl := by
      rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = orl := by
      rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = ll := by
      rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
    have g24_12 : reg n24 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb24]; simp +decide only [runBlock, BInstr.run, svL3246, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_18, g23_19, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_70
    have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_74
    have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m24]; exact w23_78
    have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m24]; exact w23_7c
    have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m24]; exact w23_80
    have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m24]; exact w23_84
    have w24_180 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_180
    have w24_184 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_184
    have w24_a20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m24]; exact w23_a20
    have w24_a24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m24]; exact w23_a24
    have w24_a28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := by rw [m24]; exact w23_a28
    have w24_1020 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_1020
    have w24_1024 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_1024
    clear w23_70 w23_1024 w23_1020 w23_a28 w23_a24 w23_a20 w23_184 w23_180 w23_84 w23_80 w23_7c w23_78 w23_74 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 rg23 W23 K23 fr23 s23 d23
    -- 0x248: lw
    obtain ⟨n25, d25, u25⟩ := s24.lw E24.self sv_at_248 (off' := 0x24A) (by decide)
      (by rw [g24_12, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s25 : St n25.mem SV n25 0x24A (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
    have m25 : n25.mem = n24.mem := u25.mem
    have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
    have t25 : Steps n0 n25 := t24.trans (.single d25)
    have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
    have E25 : SvCode n25.mem := E24.fr F fr25
    have V25 : SvSaves B n25.mem v := V24.same m25
    have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
    have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
    have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
    have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_8]
    have g25_9 : reg n25 (9 : Fin 32) = trp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_9]
    have g25_10 : reg n25 a0 = op19 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_10]
    have g25_12 : reg n25 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_12]
    have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
    have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
    have g25_21 : reg n25 (21 : Fin 32) = lp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
    have g25_22 : reg n25 (22 : Fin 32) = orp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
    have g25_23 : reg n25 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
    have g25_24 : reg n25 (24 : Fin 32) = sgl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_24]
    have g25_25 : reg n25 (25 : Fin 32) = orl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
    have g25_26 : reg n25 (26 : Fin 32) = ll := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
    have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
    have g25_11 : reg n25 a1 = BitVec.ofNat 32 ol19 := by
      rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g24_12, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, w24_a24]
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m25]; exact keep_kk24
    clear keep_kk24
    have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m25]; exact w24_70
    have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_74
    have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m25]; exact w24_78
    have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m25]; exact w24_7c
    have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m25]; exact w24_80
    have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m25]; exact w24_84
    have w25_180 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_180
    have w25_184 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_184
    have w25_a20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m25]; exact w24_a20
    have w25_a24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m25]; exact w24_a24
    have w25_a28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := by rw [m25]; exact w24_a28
    have w25_1020 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m25]; exact w24_1020
    have w25_1024 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_1024
    clear w24_1024 w24_1020 w24_a28 w24_a24 w24_a20 w24_184 w24_180 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 g24_12 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_19 g24_18 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
    -- 0x24A: lw
    obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_24a (off' := 0x24C) (by decide)
      (by rw [g25_12, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s26 : St n26.mem SV n26 0x24C (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans (.single d26)
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
    have g26_9 : reg n26 (9 : Fin 32) = trp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
    have g26_10 : reg n26 a0 = op19 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_10]
    have g26_11 : reg n26 a1 = BitVec.ofNat 32 ol19 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_11]
    have g26_12 : reg n26 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_12]
    have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
    have g26_21 : reg n26 (21 : Fin 32) = lp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = orp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = sgl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = orl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = ll := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
    have g26_8 : reg n26 (8 : Fin 32) = prp19 + BitVec.ofNat 32 pu19.header := by
      rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g25_12, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr, w25_a28]
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m26]; exact keep_kk25
    clear keep_kk25
    have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_70
    have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_74
    have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m26]; exact w25_78
    have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m26]; exact w25_7c
    have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m26]; exact w25_80
    have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m26]; exact w25_84
    have w26_180 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_180
    have w26_184 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_184
    have w26_a20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m26]; exact w25_a20
    have w26_a24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m26]; exact w25_a24
    have w26_a28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := by rw [m26]; exact w25_a28
    have w26_1020 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_1020
    have w26_1024 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_1024
    clear w25_1024 w25_1020 w25_a28 w25_a24 w25_a20 w25_184 w25_180 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 g25_11 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_19 g25_18 g25_12 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
    -- 0x24C
    obtain ⟨n27, c27, u27⟩ := s26.block svL324c E26.self svL324c_end
      ⟨trivial, trivial, trivial, trivial⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have s27 : St n27.mem SV n27 0x256 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have rb27 : ∀ q, reg n27 q = (runBlock svL324c (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans c27
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by
      rw [rb27, runBlock_reg _ _ _ sp s26.zero (by decide), g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb27, runBlock_reg _ _ _ (3 : Fin 32) s26.zero (by decide), g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb27, runBlock_reg _ _ _ (4 : Fin 32) s26.zero (by decide), g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = prp19 + BitVec.ofNat 32 pu19.header := by
      rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = trp := by
      rw [rb27, runBlock_reg _ _ _ (9 : Fin 32) s26.zero (by decide), g26_9]
    have g27_10 : reg n27 a0 = op19 := by
      rw [rb27, runBlock_reg _ _ _ a0 s26.zero (by decide), g26_10]
    have g27_11 : reg n27 a1 = BitVec.ofNat 32 ol19 := by
      rw [rb27, runBlock_reg _ _ _ a1 s26.zero (by decide), g26_11]
    have g27_18 : reg n27 (18 : Fin 32) = out := by
      rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by
      rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
    have g27_21 : reg n27 (21 : Fin 32) = lp := by
      rw [rb27, runBlock_reg _ _ _ (21 : Fin 32) s26.zero (by decide), g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = orp := by
      rw [rb27, runBlock_reg _ _ _ (22 : Fin 32) s26.zero (by decide), g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by
      rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = sgl := by
      rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = orl := by
      rw [rb27, runBlock_reg _ _ _ (25 : Fin 32) s26.zero (by decide), g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = ll := by
      rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
    have g27_12 : reg n27 a2 = BitVec.ofNat 32 (img% svConstAddress + 0x28) := by
      rw [rb27]; simp +decide only [runBlock, BInstr.run, svL324c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_10, g26_11, g26_12, g26_18, g26_19, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g27_13 : reg n27 a3 = BitVec.ofNat 32 0x8 := by
      rw [rb27]; simp +decide only [runBlock, BInstr.run, svL324c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_10, g26_11, g26_12, g26_18, g26_19, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m27]; exact keep_kk26
    clear keep_kk26
    have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_70
    have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_74
    have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m27]; exact w26_78
    have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m27]; exact w26_7c
    have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m27]; exact w26_80
    have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m27]; exact w26_84
    have w27_180 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_180
    have w27_184 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_184
    have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m27]; exact w26_a20
    have w27_a24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m27]; exact w26_a24
    have w27_a28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := by rw [m27]; exact w26_a28
    have w27_1020 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_1020
    have w27_1024 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_1024
    clear w26_1024 w26_1020 w26_a28 w26_a24 w26_a20 w26_184 w26_180 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 g26_8 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_19 g26_18 g26_12 g26_11 g26_10 g26_9 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
    -- 0x256: sv_sneF
    obtain ⟨n28, c28, s28, rk28, a0_28, K28, fr28⟩ := sv_sneF (pl := ol19) (ql := 8)
      F E27 s27 sv_at_256 sv_at_25a (by decide) (by decide) g27_2
      g27_10 g27_11 g27_12 g27_13 (.inl (((tb_in.restW hr2).rawN hr9).algOid hr19)) (.inr ⟨by decide, by decide⟩)
    have t28 : Steps n0 n28 := t27.trans c28
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.keepL K28 (by decide)
    rw [sv_mbRo F fR27 (.inl (((tb_in.restW hr2).rawN hr9).algOid hr19)), sv_mbRo F fR27 (.inr ⟨by decide, by decide⟩)] at a0_28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rk28 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk28 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk28 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = prp19 + BitVec.ofNat 32 pu19.header := by rw [rk28 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = trp := by rw [rk28 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_9]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rk28 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rk28 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_19]
    have g28_21 : reg n28 (21 : Fin 32) = lp := by rw [rk28 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = orp := by rw [rk28 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rk28 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = sgl := by rw [rk28 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = orl := by rw [rk28 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = ll := by rw [rk28 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk28 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_27]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := keep_kk27.trans K28
    clear keep_kk27
    have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K28.w32 (by decide) (by decide)).trans w27_70
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K28.w32 (by decide) (by decide)).trans w27_74
    have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K28.w32 (by decide) (by decide)).trans w27_78
    have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K28.w32 (by decide) (by decide)).trans w27_7c
    have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K28.w32 (by decide) (by decide)).trans w27_80
    have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K28.w32 (by decide) (by decide)).trans w27_84
    have w28_180 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K28.w32 (by decide) (by decide)).trans w27_180
    have w28_184 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K28.w32 (by decide) (by decide)).trans w27_184
    have w28_a20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := (K28.w32 (by decide) (by decide)).trans w27_a20
    have w28_a24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := (K28.w32 (by decide) (by decide)).trans w27_a24
    have w28_a28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := (K28.w32 (by decide) (by decide)).trans w27_a28
    have w28_1020 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K28.w32 (by decide) (by decide)).trans w27_1020
    have w28_1024 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K28.w32 (by decide) (by decide)).trans w27_1024
    clear w27_1024 w27_1020 w27_a28 w27_a24 w27_a20 w27_184 w27_180 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 g27_13 g27_12 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_19 g27_18 g27_11 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
    by_cases ho_28 : memBytes M0 op19 ol19 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x28)) 8
    · have g28_10 : reg n28 a0 = BitVec.ofNat 32 0 := by rw [a0_28, ite_eq_left ho_28]; rfl
      -- 0x25E: branch, not taken
      obtain ⟨n29, d29, u29⟩ := s28.notTaken E28.self 0x262 sv_at_25e
        (by decide) (by rw [g28_10, s28.zero]; decide)
      have s29 : St n29.mem SV n29 0x262 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
      have m29 : n29.mem = n28.mem := u29.mem
      have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
      have t29 : Steps n0 n29 := t28.trans (.single d29)
      have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
      have E29 : SvCode n29.mem := E28.fr F fr29
      have V29 : SvSaves B n29.mem v := V28.same m29
      have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
      have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
      have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
      have g29_8 : reg n29 (8 : Fin 32) = prp19 + BitVec.ofNat 32 pu19.header := by rw [u29.regs, g28_8]
      have g29_9 : reg n29 (9 : Fin 32) = trp := by rw [u29.regs, g28_9]
      have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x0 := by rw [u29.regs, g28_10]
      have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
      have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
      have g29_21 : reg n29 (21 : Fin 32) = lp := by rw [u29.regs, g28_21]
      have g29_22 : reg n29 (22 : Fin 32) = orp := by rw [u29.regs, g28_22]
      have g29_23 : reg n29 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u29.regs, g28_23]
      have g29_24 : reg n29 (24 : Fin 32) = sgl := by rw [u29.regs, g28_24]
      have g29_25 : reg n29 (25 : Fin 32) = orl := by rw [u29.regs, g28_25]
      have g29_26 : reg n29 (26 : Fin 32) = ll := by rw [u29.regs, g28_26]
      have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u29.regs, g28_27]
      have keep_kk29 : SvKeepL B n0.mem n29.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m29]; exact keep_kk28
      clear keep_kk28
      have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_70
      have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_74
      have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m29]; exact w28_78
      have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m29]; exact w28_7c
      have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m29]; exact w28_80
      have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m29]; exact w28_84
      have w29_180 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_180
      have w29_184 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_184
      have w29_a20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m29]; exact w28_a20
      have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m29]; exact w28_a24
      have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := by rw [m29]; exact w28_a28
      have w29_1020 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_1020
      have w29_1024 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_1024
      clear w28_1024 w28_1020 w28_a28 w28_a24 w28_a20 w28_184 w28_180 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 K28 a0_28 rk28 s28 c28
      -- 0x262: branch, taken
      obtain ⟨n30, d30, u30⟩ := s29.taken E29.self 0x966 sv_at_262
        (by decide) (by rw [g29_8, s29.zero]; exact br_bne_t (((tb_in.restW hr2).rawN hr9).algParams hr19))
      have s30 : St n30.mem SV n30 0x966 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
      have m30 : n30.mem = n29.mem := u30.mem
      have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
      have t30 : Steps n0 n30 := t29.trans (.single d30)
      have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
      have E30 : SvCode n30.mem := E29.fr F fr30
      have V30 : SvSaves B n30.mem v := V29.same m30
      have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
      have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
      have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
      have g30_8 : reg n30 (8 : Fin 32) = prp19 + BitVec.ofNat 32 pu19.header := by rw [u30.regs, g29_8]
      have g30_9 : reg n30 (9 : Fin 32) = trp := by rw [u30.regs, g29_9]
      have g30_10 : reg n30 a0 = BitVec.ofNat 32 0x0 := by rw [u30.regs, g29_10]
      have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
      have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
      have g30_21 : reg n30 (21 : Fin 32) = lp := by rw [u30.regs, g29_21]
      have g30_22 : reg n30 (22 : Fin 32) = orp := by rw [u30.regs, g29_22]
      have g30_23 : reg n30 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u30.regs, g29_23]
      have g30_24 : reg n30 (24 : Fin 32) = sgl := by rw [u30.regs, g29_24]
      have g30_25 : reg n30 (25 : Fin 32) = orl := by rw [u30.regs, g29_25]
      have g30_26 : reg n30 (26 : Fin 32) = ll := by rw [u30.regs, g29_26]
      have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u30.regs, g29_27]
      have keep_kk30 : SvKeepL B n0.mem n30.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m30]; exact keep_kk29
      clear keep_kk29
      have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m30]; exact w29_70
      have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_74
      have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m30]; exact w29_78
      have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m30]; exact w29_7c
      have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m30]; exact w29_80
      have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m30]; exact w29_84
      have w30_180 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_180
      have w30_184 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_184
      have w30_a20 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m30]; exact w29_a20
      have w30_a24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m30]; exact w29_a24
      have w30_a28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := by rw [m30]; exact w29_a28
      have w30_1020 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m30]; exact w29_1020
      have w30_1024 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_1024
      clear w29_1024 w29_1020 w29_a28 w29_a24 w29_a20 w29_184 w29_180 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_19 g29_18 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29 g28_10
      exact .inl ⟨(fun ⟨tl2', h0', ip2', il2', h1', h2', tl9', h3', op19', ol19', h4', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr2b] at h1'; cases h1'; rw [hr9] at h3'; cases h3'; rw [hr19] at h4'; cases h4'), sv_fail F E30 s30 t30 (fun x hx => (fR30 x hx).trans (fM x hx).symm) V30 hret g30_2 g30_18 hO g30_3 g30_4⟩
    have g28_10 : reg n28 a0 = BitVec.ofNat 32 1 := by rw [a0_28, ite_eq_right ho_28]; rfl
    -- 0x25E: branch, taken
    obtain ⟨n29, d29, u29⟩ := s28.taken E28.self 0x966 sv_at_25e
      (by decide) (by rw [g28_10, s28.zero]; decide)
    have s29 : St n29.mem SV n29 0x966 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = prp19 + BitVec.ofNat 32 pu19.header := by rw [u29.regs, g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = trp := by rw [u29.regs, g28_9]
    have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x1 := by rw [u29.regs, g28_10]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
    have g29_21 : reg n29 (21 : Fin 32) = lp := by rw [u29.regs, g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = orp := by rw [u29.regs, g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u29.regs, g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = sgl := by rw [u29.regs, g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = orl := by rw [u29.regs, g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = ll := by rw [u29.regs, g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u29.regs, g28_27]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_70
    have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_74
    have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m29]; exact w28_78
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m29]; exact w28_7c
    have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m29]; exact w28_80
    have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m29]; exact w28_84
    have w29_180 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_180
    have w29_184 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_184
    have w29_a20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m29]; exact w28_a20
    have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m29]; exact w28_a24
    have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = prp19 + BitVec.ofNat 32 pu19.header := by rw [m29]; exact w28_a28
    have w29_1020 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_1020
    have w29_1024 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_1024
    clear w28_1024 w28_1020 w28_a28 w28_a24 w28_a20 w28_184 w28_180 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 K28 a0_28 rk28 s28 c28
    exact .inl ⟨(fun ⟨tl2', h0', ip2', il2', h1', h2', tl9', h3', op19', ol19', h4', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr2b] at h1'; cases h1'; rw [hr9] at h3'; cases h3'; rw [hr19] at h4'; cases h4'), sv_fail F E29 s29 t29 (fun x hx => (fR29 x hx).trans (fM x hx).symm) V29 hret g29_2 g29_18 hO g29_3 g29_4⟩
  rw [hr19] at R19
  obtain ⟨y0_19, y4_19, y8_19⟩ := R19
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8)] := keep_kk18.trans K19
  clear keep_kk18
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K19.w32 (by decide) (by decide)).trans w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K19.w32 (by decide) (by decide)).trans w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K19.w32 (by decide) (by decide)).trans w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K19.w32 (by decide) (by decide)).trans w18_84
  have w19_180 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_180
  have w19_184 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_184
  have w19_1020 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K19.w32 (by decide) (by decide)).trans w18_1020
  have w19_1024 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_1024
  have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := y0_19
  have w19_a24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := y4_19
  have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := y8_19
  clear b18_a30 w18_102c w18_1028 w18_1024 w18_1020 w18_a2c w18_a28 w18_a24 w18_a20 w18_184 w18_180 w18_84 w18_80 w18_7c w18_78 g18_11 g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  -- 0x23A: lw
  obtain ⟨n20, d20, u20⟩ := s19.lw E19.self sv_at_23a (off' := 0x23E) (by decide)
    (by rw [g19_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s20 : St n20.mem SV n20 0x23E (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = trp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, upd_ne (by decide) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_19]
  have g20_21 : reg n20 (21 : Fin 32) = lp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = orp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = sgl := by rw [u20.regs, upd_ne (by decide) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = orl := by rw [u20.regs, upd_ne (by decide) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = ll := by rw [u20.regs, upd_ne (by decide) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_27]
  have g20_10 : reg n20 a0 = op19 := by
    rw [u20.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g19_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w19_a20]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m20]; exact w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m20]; exact w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m20]; exact w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m20]; exact w19_84
  have w20_180 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m20]; exact w19_180
  have w20_184 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m20]; exact w19_184
  have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m20]; exact w19_a20
  have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m20]; exact w19_a24
  have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := by rw [m20]; exact w19_a28
  have w20_1020 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_1020
  have w20_1024 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m20]; exact w19_1024
  clear w19_a28 w19_a24 w19_a20 w19_1024 w19_1020 w19_184 w19_180 w19_84 w19_80 w19_7c w19_78 y8_19 y4_19 y0_19 g19_2 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 V19 E19 fR19 t19 fr19 A19 K19 rk19 sp19 s19 c19
  -- 0x23E: branch, not taken
  obtain ⟨n21, d21, u21⟩ := s20.notTaken E20.self 0x242 sv_at_23e
    (by decide) (by rw [g20_10, s20.zero]; exact br_beq_f (((tb_in.restW hr2).rawN hr9).algOid hr19).pos_ne)
  have s21 : St n21.mem SV n21 0x242 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u21.regs, g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = trp := by rw [u21.regs, g20_9]
  have g21_10 : reg n21 a0 = op19 := by rw [u21.regs, g20_10]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, g20_19]
  have g21_21 : reg n21 (21 : Fin 32) = lp := by rw [u21.regs, g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = orp := by rw [u21.regs, g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u21.regs, g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = sgl := by rw [u21.regs, g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = orl := by rw [u21.regs, g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = ll := by rw [u21.regs, g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u21.regs, g20_27]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m21]; exact w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m21]; exact w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m21]; exact w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m21]; exact w20_84
  have w21_180 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_180
  have w21_184 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_184
  have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m21]; exact w20_a20
  have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m21]; exact w20_a24
  have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := by rw [m21]; exact w20_a28
  have w21_1020 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_1020
  have w21_1024 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_1024
  clear w20_1024 w20_1020 w20_a28 w20_a24 w20_a20 w20_184 w20_180 w20_84 w20_80 w20_7c w20_78 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
  -- 0x242: sw
  obtain ⟨n22, d22, s22, fr22, K22, W22, rg22⟩ := sv_sw F E21 s21 sv_at_242 (off' := 0x244) (c := 0x74)
    (by decide) (by rw [g21_2]; sv_addr) (by decide) (by decide)
  have t22 : Steps n0 n22 := t21.trans d22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keep K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [rg22 sp, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg22 (3 : Fin 32), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg22 (4 : Fin 32), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [rg22 (8 : Fin 32), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = trp := by rw [rg22 (9 : Fin 32), g21_9]
  have g22_10 : reg n22 a0 = op19 := by rw [rg22 a0, g21_10]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rg22 (18 : Fin 32), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rg22 (19 : Fin 32), g21_19]
  have g22_21 : reg n22 (21 : Fin 32) = lp := by rw [rg22 (21 : Fin 32), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = orp := by rw [rg22 (22 : Fin 32), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg22 (23 : Fin 32), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = sgl := by rw [rg22 (24 : Fin 32), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = orl := by rw [rg22 (25 : Fin 32), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = ll := by rw [rg22 (26 : Fin 32), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg22 (27 : Fin 32), g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4)] := keep_kk21.trans K22.toL
  clear keep_kk21
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K22.w32 (by decide) (by decide)).trans w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K22.w32 (by decide) (by decide)).trans w21_7c
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K22.w32 (by decide) (by decide)).trans w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K22.w32 (by decide) (by decide)).trans w21_84
  have w22_180 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K22.w32 (by decide) (by decide)).trans w21_180
  have w22_184 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K22.w32 (by decide) (by decide)).trans w21_184
  have w22_a20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := (K22.w32 (by decide) (by decide)).trans w21_a20
  have w22_a24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := (K22.w32 (by decide) (by decide)).trans w21_a24
  have w22_a28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := (K22.w32 (by decide) (by decide)).trans w21_a28
  have w22_1020 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K22.w32 (by decide) (by decide)).trans w21_1020
  have w22_1024 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K22.w32 (by decide) (by decide)).trans w21_1024
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [W22, g21_8]
  clear w21_1024 w21_1020 w21_a28 w21_a24 w21_a20 w21_184 w21_180 w21_84 w21_80 w21_7c w21_78 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_19 g21_18 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0x244: sw
  obtain ⟨n23, d23, s23, fr23, K23, W23, rg23⟩ := sv_sw F E22 s22 sv_at_244 (off' := 0x246) (c := 0x70)
    (by decide) (by rw [g22_2]; sv_addr) (by decide) (by decide)
  have t23 : Steps n0 n23 := t22.trans d23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.keep K23 (by decide)
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [rg23 sp, g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg23 (3 : Fin 32), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg23 (4 : Fin 32), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [rg23 (8 : Fin 32), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = trp := by rw [rg23 (9 : Fin 32), g22_9]
  have g23_10 : reg n23 a0 = op19 := by rw [rg23 a0, g22_10]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [rg23 (18 : Fin 32), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [rg23 (19 : Fin 32), g22_19]
  have g23_21 : reg n23 (21 : Fin 32) = lp := by rw [rg23 (21 : Fin 32), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = orp := by rw [rg23 (22 : Fin 32), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg23 (23 : Fin 32), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = sgl := by rw [rg23 (24 : Fin 32), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = orl := by rw [rg23 (25 : Fin 32), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = ll := by rw [rg23 (26 : Fin 32), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg23 (27 : Fin 32), g22_27]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := keep_kk22.trans K23.toL
  clear keep_kk22
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K23.w32 (by decide) (by decide)).trans w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K23.w32 (by decide) (by decide)).trans w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K23.w32 (by decide) (by decide)).trans w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K23.w32 (by decide) (by decide)).trans w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K23.w32 (by decide) (by decide)).trans w22_84
  have w23_180 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K23.w32 (by decide) (by decide)).trans w22_180
  have w23_184 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K23.w32 (by decide) (by decide)).trans w22_184
  have w23_a20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := (K23.w32 (by decide) (by decide)).trans w22_a20
  have w23_a24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := (K23.w32 (by decide) (by decide)).trans w22_a24
  have w23_a28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := (K23.w32 (by decide) (by decide)).trans w22_a28
  have w23_1020 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K23.w32 (by decide) (by decide)).trans w22_1020
  have w23_1024 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K23.w32 (by decide) (by decide)).trans w22_1024
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [W23, g22_23]
  clear w22_74 w22_1024 w22_1020 w22_a28 w22_a24 w22_a20 w22_184 w22_180 w22_84 w22_80 w22_7c w22_78 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_19 g22_18 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 rg22 W22 K22 fr22 s22 d22
  -- 0x246
  obtain ⟨n24, c24, u24⟩ := s23.block svL3246 E23.self svL3246_end
    ⟨trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem SV n24 0x248 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock svL3246 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans c24
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by
    rw [rb24, runBlock_reg _ _ _ sp s23.zero (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (3 : Fin 32) s23.zero (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (4 : Fin 32) s23.zero (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = trp := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
  have g24_10 : reg n24 a0 = op19 := by
    rw [rb24, runBlock_reg _ _ _ a0 s23.zero (by decide), g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_21 : reg n24 (21 : Fin 32) = lp := by
    rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = orp := by
    rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = sgl := by
    rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = orl := by
    rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = ll := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_12 : reg n24 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svL3246, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_18, g23_19, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m24]; exact w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m24]; exact w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m24]; exact w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m24]; exact w23_84
  have w24_180 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_180
  have w24_184 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_184
  have w24_a20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m24]; exact w23_a20
  have w24_a24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m24]; exact w23_a24
  have w24_a28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := by rw [m24]; exact w23_a28
  have w24_1020 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_1020
  have w24_1024 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_1024
  clear w23_70 w23_1024 w23_1020 w23_a28 w23_a24 w23_a20 w23_184 w23_180 w23_84 w23_80 w23_7c w23_78 w23_74 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 rg23 W23 K23 fr23 s23 d23
  -- 0x248: lw
  obtain ⟨n25, d25, u25⟩ := s24.lw E24.self sv_at_248 (off' := 0x24A) (by decide)
    (by rw [g24_12, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s25 : St n25.mem SV n25 0x24A (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans (.single d25)
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = trp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_9]
  have g25_10 : reg n25 a0 = op19 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_10]
  have g25_12 : reg n25 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_12]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
  have g25_21 : reg n25 (21 : Fin 32) = lp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = orp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = sgl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = orl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = ll := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
  have g25_11 : reg n25 a1 = BitVec.ofNat 32 ol19 := by
    rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g24_12, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, w24_a24]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m25]; exact w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m25]; exact w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m25]; exact w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m25]; exact w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m25]; exact w24_84
  have w25_180 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_180
  have w25_184 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_184
  have w25_a20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m25]; exact w24_a20
  have w25_a24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m25]; exact w24_a24
  have w25_a28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := by rw [m25]; exact w24_a28
  have w25_1020 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m25]; exact w24_1020
  have w25_1024 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_1024
  clear w24_1024 w24_1020 w24_a28 w24_a24 w24_a20 w24_184 w24_180 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 g24_12 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_19 g24_18 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0x24A: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_24a (off' := 0x24C) (by decide)
    (by rw [g25_12, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0x24C (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_9 : reg n26 (9 : Fin 32) = trp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
  have g26_10 : reg n26 a0 = op19 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_10]
  have g26_11 : reg n26 a1 = BitVec.ofNat 32 ol19 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_11]
  have g26_12 : reg n26 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_12]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_21 : reg n26 (21 : Fin 32) = lp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = orp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = sgl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = orl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = ll := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_8 : reg n26 (8 : Fin 32) = 0 := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_12, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr, w25_a28]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m26]; exact w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m26]; exact w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m26]; exact w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m26]; exact w25_84
  have w26_180 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_180
  have w26_184 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_184
  have w26_a20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m26]; exact w25_a20
  have w26_a24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m26]; exact w25_a24
  have w26_a28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := by rw [m26]; exact w25_a28
  have w26_1020 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_1020
  have w26_1024 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_1024
  clear w25_1024 w25_1020 w25_a28 w25_a24 w25_a20 w25_184 w25_180 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 g25_11 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_19 g25_18 g25_12 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
  -- 0x24C
  obtain ⟨n27, c27, u27⟩ := s26.block svL324c E26.self svL324c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem SV n27 0x256 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock svL324c (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans c27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by
    rw [rb27, runBlock_reg _ _ _ sp s26.zero (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (3 : Fin 32) s26.zero (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (4 : Fin 32) s26.zero (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = 0 := by
    rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = trp := by
    rw [rb27, runBlock_reg _ _ _ (9 : Fin 32) s26.zero (by decide), g26_9]
  have g27_10 : reg n27 a0 = op19 := by
    rw [rb27, runBlock_reg _ _ _ a0 s26.zero (by decide), g26_10]
  have g27_11 : reg n27 a1 = BitVec.ofNat 32 ol19 := by
    rw [rb27, runBlock_reg _ _ _ a1 s26.zero (by decide), g26_11]
  have g27_18 : reg n27 (18 : Fin 32) = out := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by
    rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
  have g27_21 : reg n27 (21 : Fin 32) = lp := by
    rw [rb27, runBlock_reg _ _ _ (21 : Fin 32) s26.zero (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = orp := by
    rw [rb27, runBlock_reg _ _ _ (22 : Fin 32) s26.zero (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = sgl := by
    rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = orl := by
    rw [rb27, runBlock_reg _ _ _ (25 : Fin 32) s26.zero (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = ll := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
  have g27_12 : reg n27 a2 = BitVec.ofNat 32 (img% svConstAddress + 0x28) := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svL324c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_10, g26_11, g26_12, g26_18, g26_19, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g27_13 : reg n27 a3 = BitVec.ofNat 32 0x8 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svL324c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_10, g26_11, g26_12, g26_18, g26_19, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m27]; exact w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m27]; exact w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m27]; exact w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m27]; exact w26_84
  have w27_180 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_180
  have w27_184 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_184
  have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m27]; exact w26_a20
  have w27_a24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m27]; exact w26_a24
  have w27_a28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := by rw [m27]; exact w26_a28
  have w27_1020 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_1020
  have w27_1024 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_1024
  clear w26_1024 w26_1020 w26_a28 w26_a24 w26_a20 w26_184 w26_180 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 g26_8 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_19 g26_18 g26_12 g26_11 g26_10 g26_9 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0x256: sv_sneF
  obtain ⟨n28, c28, s28, rk28, a0_28, K28, fr28⟩ := sv_sneF (pl := ol19) (ql := 8)
    F E27 s27 sv_at_256 sv_at_25a (by decide) (by decide) g27_2
    g27_10 g27_11 g27_12 g27_13 (.inl (((tb_in.restW hr2).rawN hr9).algOid hr19)) (.inr ⟨by decide, by decide⟩)
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keepL K28 (by decide)
  rw [sv_mbRo F fR27 (.inl (((tb_in.restW hr2).rawN hr9).algOid hr19)), sv_mbRo F fR27 (.inr ⟨by decide, by decide⟩)] at a0_28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rk28 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk28 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk28 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = 0 := by rw [rk28 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = trp := by rw [rk28 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rk28 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rk28 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_19]
  have g28_21 : reg n28 (21 : Fin 32) = lp := by rw [rk28 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = orp := by rw [rk28 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rk28 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = sgl := by rw [rk28 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = orl := by rw [rk28 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = ll := by rw [rk28 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk28 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := keep_kk27.trans K28
  clear keep_kk27
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K28.w32 (by decide) (by decide)).trans w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K28.w32 (by decide) (by decide)).trans w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K28.w32 (by decide) (by decide)).trans w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K28.w32 (by decide) (by decide)).trans w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K28.w32 (by decide) (by decide)).trans w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K28.w32 (by decide) (by decide)).trans w27_84
  have w28_180 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K28.w32 (by decide) (by decide)).trans w27_180
  have w28_184 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K28.w32 (by decide) (by decide)).trans w27_184
  have w28_a20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := (K28.w32 (by decide) (by decide)).trans w27_a20
  have w28_a24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := (K28.w32 (by decide) (by decide)).trans w27_a24
  have w28_a28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := (K28.w32 (by decide) (by decide)).trans w27_a28
  have w28_1020 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K28.w32 (by decide) (by decide)).trans w27_1020
  have w28_1024 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K28.w32 (by decide) (by decide)).trans w27_1024
  clear w27_1024 w27_1020 w27_a28 w27_a24 w27_a20 w27_184 w27_180 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 g27_13 g27_12 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_19 g27_18 g27_11 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
  by_cases hz_28 : memBytes M0 op19 ol19 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x28)) 8
  rotate_left
  · have g28_10 : reg n28 a0 = BitVec.ofNat 32 1 := by rw [a0_28, ite_eq_right hz_28]; rfl
    -- 0x25E: branch, taken
    obtain ⟨n29, d29, u29⟩ := s28.taken E28.self 0x966 sv_at_25e
      (by decide) (by rw [g28_10, s28.zero]; decide)
    have s29 : St n29.mem SV n29 0x966 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = 0 := by rw [u29.regs, g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = trp := by rw [u29.regs, g28_9]
    have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x1 := by rw [u29.regs, g28_10]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
    have g29_21 : reg n29 (21 : Fin 32) = lp := by rw [u29.regs, g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = orp := by rw [u29.regs, g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u29.regs, g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = sgl := by rw [u29.regs, g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = orl := by rw [u29.regs, g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = ll := by rw [u29.regs, g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u29.regs, g28_27]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_70
    have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_74
    have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m29]; exact w28_78
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m29]; exact w28_7c
    have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m29]; exact w28_80
    have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m29]; exact w28_84
    have w29_180 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_180
    have w29_184 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_184
    have w29_a20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m29]; exact w28_a20
    have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m29]; exact w28_a24
    have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := by rw [m29]; exact w28_a28
    have w29_1020 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_1020
    have w29_1024 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_1024
    clear w28_1024 w28_1020 w28_a28 w28_a24 w28_a20 w28_184 w28_180 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 K28 a0_28 rk28 s28 c28
    exact .inl ⟨(fun ⟨tl2', h0', ip2', il2', h1', h2', tl9', h3', op19', ol19', h4', h5', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr2b] at h1'; cases h1'; rw [hr9] at h3'; cases h3'; rw [hr19] at h4'; cases h4'; exact hz_28 h5'), sv_fail F E29 s29 t29 (fun x hx => (fR29 x hx).trans (fM x hx).symm) V29 hret g29_2 g29_18 hO g29_3 g29_4⟩
  have g28_10 : reg n28 a0 = BitVec.ofNat 32 0 := by rw [a0_28, ite_eq_left hz_28]; rfl
  -- 0x25E: branch, not taken
  obtain ⟨n29, d29, u29⟩ := s28.notTaken E28.self 0x262 sv_at_25e
    (by decide) (by rw [g28_10, s28.zero]; decide)
  have s29 : St n29.mem SV n29 0x262 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = 0 := by rw [u29.regs, g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = trp := by rw [u29.regs, g28_9]
  have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x0 := by rw [u29.regs, g28_10]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
  have g29_21 : reg n29 (21 : Fin 32) = lp := by rw [u29.regs, g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = orp := by rw [u29.regs, g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u29.regs, g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = sgl := by rw [u29.regs, g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = orl := by rw [u29.regs, g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = ll := by rw [u29.regs, g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u29.regs, g28_27]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_70
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m29]; exact w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m29]; exact w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m29]; exact w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m29]; exact w28_84
  have w29_180 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_180
  have w29_184 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_184
  have w29_a20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m29]; exact w28_a20
  have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m29]; exact w28_a24
  have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := by rw [m29]; exact w28_a28
  have w29_1020 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_1020
  have w29_1024 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_1024
  clear w28_1024 w28_1020 w28_a28 w28_a24 w28_a20 w28_184 w28_180 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 K28 a0_28 rk28 s28 c28
  -- 0x262: branch, not taken
  obtain ⟨n30, d30, u30⟩ := s29.notTaken E29.self 0x266 sv_at_262
    (by decide) (by rw [g29_8, s29.zero]; decide)
  have s30 : St n30.mem SV n30 0x266 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = 0 := by rw [u30.regs, g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = trp := by rw [u30.regs, g29_9]
  have g30_10 : reg n30 a0 = BitVec.ofNat 32 0x0 := by rw [u30.regs, g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
  have g30_21 : reg n30 (21 : Fin 32) = lp := by rw [u30.regs, g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = orp := by rw [u30.regs, g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u30.regs, g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = sgl := by rw [u30.regs, g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = orl := by rw [u30.regs, g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = ll := by rw [u30.regs, g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u30.regs, g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0xA20, 0x8), (0x180, 0x8), (0xA20, 0x11), (0x180, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m30]; exact w29_70
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m30]; exact w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m30]; exact w29_7c
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m30]; exact w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m30]; exact w29_84
  have w30_180 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_180
  have w30_184 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_184
  have w30_a20 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = op19 := by rw [m30]; exact w29_a20
  have w30_a24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 ol19 := by rw [m30]; exact w29_a24
  have w30_a28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = 0 := by rw [m30]; exact w29_a28
  have w30_1020 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m30]; exact w29_1020
  have w30_1024 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_1024
  clear w29_1024 w29_1020 w29_a28 w29_a24 w29_a20 w29_184 w29_180 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_19 g29_18 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29 g28_10
  exact .inr ⟨tl2, hr2, ip2, il2, hr2b, hz_6, tl9, hr9, op19, ol19, hr19, hz_28, n30, t30, s30, E30, V30, fR30, g30_2, g30_3, g30_4, g30_8, g30_9, g30_18, g30_19, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, w30_70, w30_74, w30_78, w30_7c, w30_80, w30_84, w30_180, w30_184, w30_a20, w30_a24, w30_a28, w30_1020, w30_1024, keep_kk30.mono (by decide)⟩

end C3.RV32.Sv
