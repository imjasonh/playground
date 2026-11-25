import C3BootProofs.Proofs.SvCs

/-!
# `sigstore::verify`: the space after a signature line's name

From the name scan at 0x1694 to the base64 groups at 0x16D4: the name isn't empty, and the base64 after the space has a multiple of four bytes.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCns1694 : List BInstr :=
  [.alu .add a0 (27 : Fin 32) (24 : Fin 32)]
theorem svCns1694_end : blockEnd sigstoreVerifyCode 0x1694 svCns1694 = some 0x1698 := by
  simp only [svCns1694]
  rw [blockEnd, sv_at_1694]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCns169c : List BInstr :=
  [.aluImm .add a0 a0 0xFFFFFFE0]
theorem svCns169c_end : blockEnd sigstoreVerifyCode 0x169C svCns169c = some 0x169E := by
  simp only [svCns169c]
  rw [blockEnd, sv_at_169c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCns1878 : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x1A]
theorem svCns1878_end : blockEnd sigstoreVerifyCode 0x1878 svCns1878 = some 0x187A := by
  simp only [svCns1878]
  rw [blockEnd, sv_at_1878]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCns16ac : List BInstr :=
  [.aluImm .add a0 (24 : Fin 32) 0x1, .alu .add (9 : Fin 32) x0 a0, .alu .sub (26 : Fin 32) (8 : Fin 32) a0]
theorem svCns16ac_end : blockEnd sigstoreVerifyCode 0x16AC svCns16ac = some 0x16B6 := by
  simp only [svCns16ac]
  rw [blockEnd, sv_at_16ac]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16b0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16b2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCns16b6 : List BInstr :=
  [.aluImm .and a0 (26 : Fin 32) 0x3]
theorem svCns16b6_end : blockEnd sigstoreVerifyCode 0x16B6 svCns16b6 = some 0x16BA := by
  simp only [svCns16b6]
  rw [blockEnd, sv_at_16b6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCns16be : List BInstr :=
  [.aluImm .add (21 : Fin 32) x0 0x0, .aluImm .srl a0 (26 : Fin 32) 0x2, .alu .add a1 (27 : Fin 32) (9 : Fin 32)]
theorem svCns16be_end : blockEnd sigstoreVerifyCode 0x16BE svCns16be = some 0x16C8 := by
  simp only [svCns16be]
  rw [blockEnd, sv_at_16be]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16c4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCns16ca : List BInstr :=
  [.aluImm .sll a0 a0 0x2]
theorem svCns16ca_end : blockEnd sigstoreVerifyCode 0x16CA svCns16ca = some 0x16CC := by
  simp only [svCns16ca]
  rw [blockEnd, sv_at_16ca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCns16cc : List BInstr :=
  [.alu .add a0 a0 a1]
theorem svCns16cc_end : blockEnd sigstoreVerifyCode 0x16CC svCns16cc = some 0x16CE := by
  simp only [svCns16cc]
  rw [blockEnd, sv_at_16cc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCns16d2 : List BInstr :=
  [.alu .add a0 x0 a1]
theorem svCns16d2_end : blockEnd sigstoreVerifyCode 0x16D2 svCns16d2 = some 0x16D4 := by
  simp only [svCns16d2]
  rw [blockEnd, sv_at_16d2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_cns {B out bp x20 x21 x22 x23 x24 x25 x26 x27 f w38 w50 kh w48 w44 kp ckp bl np ni nl : Word} {sg : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x1694 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (b0_14 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0))
    (q0_1fc : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (g0_8 : reg n0 (8 : Fin 32) = nl)
    (g0_24 : reg n0 (24 : Fin 32) = ni)
    (g0_27 : reg n0 (27 : Fin 32) = np)
    (pa_in : SvIn B (np + ni) 1)
    (hsp : M0 (np + ni) = 0x20) :
    (¬ ((ni ≠ 0) ∧ (((nl) - ((ni) + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((ni ≠ 0) ∧
    (((nl) - ((ni) + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x16D4 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = nl ∧
        reg n' (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 ∧
        reg n' a0 = (np) + ((ni) + BitVec.ofNat 32 0x1) ∧
        reg n' a1 = (np) + ((ni) + BitVec.ofNat 32 0x1) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = ni ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) ∧
        reg n' (27 : Fin 32) = np ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = (aluEval .sll (((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + ((np) + ((ni) + BitVec.ofNat 32 0x1)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = (np) + ((ni) + BitVec.ofNat 32 0x1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0xC, 0x4), (0x8, 0x4), (0x10, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x1694
  obtain ⟨n1, c1, u1⟩ := s0.block svCns1694 E0.self svCns1694_end
    ⟨trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x1698 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svCns1694 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_8 : reg n1 (8 : Fin 32) = nl := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
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
  have g1_24 : reg n1 (24 : Fin 32) = ni := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = np := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = (np) + (ni) := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svCns1694, upd, ↓reduceIte]; rw [g0_27, g0_24] <;> rfl
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_18 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m1]; exact w0_18
  have w1_24 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m1]; exact w0_24
  have w1_28 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m1]; exact w0_28
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m1]; exact w0_30
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m1]; exact w0_34
  have w1_38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m1]; exact w0_38
  have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m1]; exact w0_44
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m1]; exact w0_48
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  have b1_14 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m1]; exact b0_14
  have q1_1fc : ∀ j, j < 63 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m1]; exact q0_1fc j hj
  -- 0x1698: lbu from the bundle
  obtain ⟨n2, d2, u2⟩ := s1.lbu E1.self sv_at_1698 (off' := 0x169C) (by decide)
  have s2 : St n2.mem SV n2 0x169C (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = nl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_8]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = ni := by rw [u2.regs, upd_ne (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = np := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_10 : reg n2 a0 = (M0 ((np) + (ni))).zeroExtend 32 := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_10, show ((np) + (ni)) + 0x0 = (np) + (ni) from BitVec.add_zero _, fR1 _ (pa_in.r0 (by decide))]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_18 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m2]; exact w1_18
  have w2_24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m2]; exact w1_24
  have w2_28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m2]; exact w1_28
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m2]; exact w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m2]; exact w1_34
  have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m2]; exact w1_38
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m2]; exact w1_44
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m2]; exact w1_48
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
  have b2_14 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m2]; exact b1_14
  have q2_1fc : ∀ j, j < 63 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m2]; exact q1_1fc j hj
  clear q1_1fc b1_14 w1_50 w1_48 w1_44 w1_38 w1_34 w1_30 w1_28 w1_24 w1_18 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x169C
  obtain ⟨n3, c3, u3⟩ := s2.block svCns169c E2.self svCns169c_end
    ⟨trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0x169E (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock svCns169c (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans c3
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by
    rw [rb3, runBlock_reg _ _ _ sp s2.zero (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (3 : Fin 32) s2.zero (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (4 : Fin 32) s2.zero (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = nl := by
    rw [rb3, runBlock_reg _ _ _ (8 : Fin 32) s2.zero (by decide), g2_8]
  have g3_18 : reg n3 (18 : Fin 32) = out := by
    rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by
    rw [rb3, runBlock_reg _ _ _ (20 : Fin 32) s2.zero (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by
    rw [rb3, runBlock_reg _ _ _ (22 : Fin 32) s2.zero (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by
    rw [rb3, runBlock_reg _ _ _ (23 : Fin 32) s2.zero (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = ni := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by
    rw [rb3, runBlock_reg _ _ _ (25 : Fin 32) s2.zero (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = np := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_10 : reg n3 a0 = (M0 ((np) + (ni))).zeroExtend 32 + 0xFFFFFFE0 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svCns169c, upd, ↓reduceIte]; rw [g2_10]; rfl
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_18 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m3]; exact w2_18
  have w3_24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m3]; exact w2_24
  have w3_28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m3]; exact w2_28
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m3]; exact w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m3]; exact w2_34
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m3]; exact w2_38
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m3]; exact w2_44
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m3]; exact w2_48
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  have b3_14 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m3]; exact b2_14
  have q3_1fc : ∀ j, j < 63 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m3]; exact q2_1fc j hj
  clear q2_1fc b2_14 w2_50 w2_48 w2_44 w2_38 w2_34 w2_30 w2_28 w2_24 w2_18 g2_10 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x169E: branch, taken
  obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x16A8 sv_at_169e
    (by decide) (by rw [g3_10, s3.zero]; exact br_beq_t ((space_iff _).mpr hsp))
  have s4 : St n4.mem SV n4 0x16A8 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = nl := by rw [u4.regs, g3_8]
  have g4_10 : reg n4 a0 = (M0 ((np) + (ni))).zeroExtend 32 + 0xFFFFFFE0 := by rw [u4.regs, g3_10]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = ni := by rw [u4.regs, g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [u4.regs, g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = np := by rw [u4.regs, g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_18 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m4]; exact w3_18
  have w4_24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m4]; exact w3_24
  have w4_28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m4]; exact w3_28
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m4]; exact w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m4]; exact w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m4]; exact w3_38
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m4]; exact w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m4]; exact w3_48
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m4]; exact w3_50
  have b4_14 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m4]; exact b3_14
  have q4_1fc : ∀ j, j < 63 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m4]; exact q3_1fc j hj
  clear q3_1fc b3_14 w3_50 w3_48 w3_44 w3_38 w3_34 w3_30 w3_28 w3_24 w3_18 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  by_cases hc0 : ni ≠ 0
  rotate_left
  · -- 0x16A8: branch, taken
    obtain ⟨n5, d5, u5⟩ := s4.taken E4.self 0x1878 sv_at_16a8
      (by decide) (by rw [g4_24, s4.zero]; exact br_beq_t (Decidable.of_not_not hc0))
    have s5 : St n5.mem SV n5 0x1878 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
    have g5_8 : reg n5 (8 : Fin 32) = nl := by rw [u5.regs, g4_8]
    have g5_10 : reg n5 a0 = (M0 ((np) + (ni))).zeroExtend 32 + 0xFFFFFFE0 := by rw [u5.regs, g4_10]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
    have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, g4_20]
    have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, g4_22]
    have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, g4_23]
    have g5_24 : reg n5 (24 : Fin 32) = ni := by rw [u5.regs, g4_24]
    have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = np := by rw [u5.regs, g4_27]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_18 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m5]; exact w4_18
    have w5_24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m5]; exact w4_24
    have w5_28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m5]; exact w4_28
    have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m5]; exact w4_30
    have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m5]; exact w4_34
    have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m5]; exact w4_38
    have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
    have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m5]; exact w4_48
    have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
    have b5_14 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m5]; exact b4_14
    have q5_1fc : ∀ j, j < 63 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_1fc j hj
    clear q4_1fc b4_14 w4_50 w4_48 w4_44 w4_38 w4_34 w4_30 w4_28 w4_24 w4_18 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    -- 0x1878
    obtain ⟨n6, c6, u6⟩ := s5.block svCns1878 E5.self svCns1878_end
      ⟨trivial, trivial⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have s6 : St n6.mem SV n6 0x187A (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have rb6 : ∀ q, reg n6 q = (runBlock svCns1878 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
    have g6_8 : reg n6 (8 : Fin 32) = nl := by
      rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
    have g6_10 : reg n6 a0 = (M0 ((np) + (ni))).zeroExtend 32 + 0xFFFFFFE0 := by
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
    have g6_24 : reg n6 (24 : Fin 32) = ni := by
      rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
    have g6_26 : reg n6 (26 : Fin 32) = x26 := by
      rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = np := by
      rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
    have g6_25 : reg n6 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb6]; simp +decide only [runBlock, BInstr.run, svCns1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_10, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_18 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m6]; exact w5_18
    have w6_24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m6]; exact w5_24
    have w6_28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m6]; exact w5_28
    have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m6]; exact w5_30
    have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m6]; exact w5_34
    have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m6]; exact w5_38
    have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
    have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m6]; exact w5_48
    have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
    have b6_14 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m6]; exact b5_14
    have q6_1fc : ∀ j, j < 63 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_1fc j hj
    clear q5_1fc b5_14 w5_50 w5_48 w5_44 w5_38 w5_34 w5_30 w5_28 w5_24 w5_18 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    -- 0x187A: j
    obtain ⟨n7, d7, u7⟩ := s6.jump E6.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s6.pc]; decide)
    have s7 : St n7.mem SV n7 0x1882 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
    have g7_8 : reg n7 (8 : Fin 32) = nl := by rw [u7.regs, g6_8]
    have g7_10 : reg n7 a0 = (M0 ((np) + (ni))).zeroExtend 32 + 0xFFFFFFE0 := by rw [u7.regs, g6_10]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = ni := by rw [u7.regs, g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u7.regs, g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = np := by rw [u7.regs, g6_27]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_18 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m7]; exact w6_18
    have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m7]; exact w6_24
    have w7_28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m7]; exact w6_28
    have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m7]; exact w6_30
    have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m7]; exact w6_34
    have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m7]; exact w6_38
    have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m7]; exact w6_44
    have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m7]; exact w6_48
    have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
    have b7_14 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m7]; exact b6_14
    have q7_1fc : ∀ j, j < 63 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m7]; exact q6_1fc j hj
    clear q6_1fc b6_14 w6_50 w6_48 w6_44 w6_38 w6_34 w6_30 w6_28 w6_24 w6_18 g6_25 g6_27 g6_26 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hc0 h0'), sv_fail_1882 F E7 s7 t7 (fun x hx => (fR7 x hx).trans (fM x hx).symm) V7 hret g7_2 g7_18 hO g7_3 g7_4 (by rw [g7_25]; sv_code)⟩
  -- 0x16A8: branch, not taken
  obtain ⟨n5, d5, u5⟩ := s4.notTaken E4.self 0x16AC sv_at_16a8
    (by decide) (by rw [g4_24, s4.zero]; exact br_beq_f hc0)
  have s5 : St n5.mem SV n5 0x16AC (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = nl := by rw [u5.regs, g4_8]
  have g5_10 : reg n5 a0 = (M0 ((np) + (ni))).zeroExtend 32 + 0xFFFFFFE0 := by rw [u5.regs, g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = ni := by rw [u5.regs, g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = np := by rw [u5.regs, g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_18 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m5]; exact w4_18
  have w5_24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m5]; exact w4_24
  have w5_28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m5]; exact w4_28
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m5]; exact w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m5]; exact w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m5]; exact w4_38
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m5]; exact w4_48
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have b5_14 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m5]; exact b4_14
  have q5_1fc : ∀ j, j < 63 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_1fc j hj
  clear q4_1fc b4_14 w4_50 w4_48 w4_44 w4_38 w4_34 w4_30 w4_28 w4_24 w4_18 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0x16AC
  obtain ⟨n6, c6, u6⟩ := s5.block svCns16ac E5.self svCns16ac_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x16B6 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svCns16ac (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_8 : reg n6 (8 : Fin 32) = nl := by
    rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
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
  have g6_24 : reg n6 (24 : Fin 32) = ni := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_27 : reg n6 (27 : Fin 32) = np := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_9 : reg n6 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svCns16ac, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_10, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_10 : reg n6 a0 = (ni) + BitVec.ofNat 32 0x1 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svCns16ac, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_10, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_26 : reg n6 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svCns16ac, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_10, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_18 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m6]; exact w5_18
  have w6_24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m6]; exact w5_24
  have w6_28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m6]; exact w5_28
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m6]; exact w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m6]; exact w5_34
  have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m6]; exact w5_38
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m6]; exact w5_48
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
  have b6_14 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m6]; exact b5_14
  have q6_1fc : ∀ j, j < 63 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_1fc j hj
  clear q5_1fc b5_14 w5_50 w5_48 w5_44 w5_38 w5_34 w5_30 w5_28 w5_24 w5_18 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x16B6
  obtain ⟨n7, c7, u7⟩ := s6.block svCns16b6 E6.self svCns16b6_end
    ⟨trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x16BA (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svCns16b6 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_8 : reg n7 (8 : Fin 32) = nl := by
    rw [rb7, runBlock_reg _ _ _ (8 : Fin 32) s6.zero (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
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
  have g7_24 : reg n7 (24 : Fin 32) = ni := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = np := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_10 : reg n7 a0 = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svCns16b6, upd, ↓reduceIte]; rw [g6_26] <;> rfl
  have keep_kk7 : SvKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_18 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m7]; exact w6_18
  have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m7]; exact w6_24
  have w7_28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m7]; exact w6_28
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m7]; exact w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m7]; exact w6_34
  have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m7]; exact w6_38
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m7]; exact w6_44
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m7]; exact w6_48
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
  have b7_14 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m7]; exact b6_14
  have q7_1fc : ∀ j, j < 63 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m7]; exact q6_1fc j hj
  clear q6_1fc b6_14 w6_50 w6_48 w6_44 w6_38 w6_34 w6_30 w6_28 w6_24 w6_18 g6_26 g6_10 g6_9 g6_27 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  by_cases h4m : ((nl) - ((ni) + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 = 0
  rotate_left
  · -- 0x16BA: branch, taken
    obtain ⟨n8, d8, u8⟩ := s7.taken E7.self 0x1878 sv_at_16ba
      (by decide) (by rw [g7_10, s7.zero]; exact br_bne_t h4m)
    have s8 : St n8.mem SV n8 0x1878 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
    have g8_8 : reg n8 (8 : Fin 32) = nl := by rw [u8.regs, g7_8]
    have g8_9 : reg n8 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by rw [u8.regs, g7_9]
    have g8_10 : reg n8 a0 = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 := by rw [u8.regs, g7_10]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = ni := by rw [u8.regs, g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by rw [u8.regs, g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = np := by rw [u8.regs, g7_27]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_18 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m8]; exact w7_18
    have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m8]; exact w7_24
    have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m8]; exact w7_28
    have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m8]; exact w7_30
    have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m8]; exact w7_34
    have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m8]; exact w7_38
    have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m8]; exact w7_44
    have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m8]; exact w7_48
    have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
    have b8_14 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m8]; exact b7_14
    have q8_1fc : ∀ j, j < 63 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m8]; exact q7_1fc j hj
    clear q7_1fc b7_14 w7_50 w7_48 w7_44 w7_38 w7_34 w7_30 w7_28 w7_24 w7_18 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
    -- 0x1878
    obtain ⟨n9, c9, u9⟩ := s8.block svCns1878 E8.self svCns1878_end
      ⟨trivial, trivial⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have s9 : St n9.mem SV n9 0x187A (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have rb9 : ∀ q, reg n9 q = (runBlock svCns1878 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
    have g9_8 : reg n9 (8 : Fin 32) = nl := by
      rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by
      rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
    have g9_10 : reg n9 a0 = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 := by
      rw [rb9, runBlock_reg _ _ _ a0 s8.zero (by decide), g8_10]
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
    have g9_24 : reg n9 (24 : Fin 32) = ni := by
      rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
    have g9_26 : reg n9 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by
      rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = np := by
      rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
    have g9_25 : reg n9 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb9]; simp +decide only [runBlock, BInstr.run, svCns1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk9 : SvKeepL B n0.mem n9.mem [] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_18 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m9]; exact w8_18
    have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m9]; exact w8_24
    have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m9]; exact w8_28
    have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m9]; exact w8_30
    have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m9]; exact w8_34
    have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m9]; exact w8_38
    have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m9]; exact w8_44
    have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m9]; exact w8_48
    have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
    have b9_14 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m9]; exact b8_14
    have q9_1fc : ∀ j, j < 63 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m9]; exact q8_1fc j hj
    clear q8_1fc b8_14 w8_50 w8_48 w8_44 w8_38 w8_34 w8_30 w8_28 w8_24 w8_18 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    -- 0x187A: j
    obtain ⟨n10, d10, u10⟩ := s9.jump E9.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s9.pc]; decide)
    have s10 : St n10.mem SV n10 0x1882 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = nl := by rw [u10.regs, g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by rw [u10.regs, g9_9]
    have g10_10 : reg n10 a0 = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 := by rw [u10.regs, g9_10]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [u10.regs, g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = ni := by rw [u10.regs, g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u10.regs, g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by rw [u10.regs, g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = np := by rw [u10.regs, g9_27]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_18 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m10]; exact w9_18
    have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m10]; exact w9_24
    have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m10]; exact w9_28
    have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m10]; exact w9_30
    have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m10]; exact w9_34
    have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m10]; exact w9_38
    have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
    have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m10]; exact w9_48
    have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
    have b10_14 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m10]; exact b9_14
    have q10_1fc : ∀ j, j < 63 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_1fc j hj
    clear q9_1fc b9_14 w9_50 w9_48 w9_44 w9_38 w9_34 w9_30 w9_28 w9_24 w9_18 g9_25 g9_27 g9_26 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
    exact .inl ⟨(fun ⟨h0', h1', _⟩ => by exact h4m h1'), sv_fail_1882 F E10 s10 t10 (fun x hx => (fR10 x hx).trans (fM x hx).symm) V10 hret g10_2 g10_18 hO g10_3 g10_4 (by rw [g10_25]; sv_code)⟩
  -- 0x16BA: branch, not taken
  obtain ⟨n8, d8, u8⟩ := s7.notTaken E7.self 0x16BE sv_at_16ba
    (by decide) (by rw [g7_10, s7.zero]; exact br_bne_f h4m)
  have s8 : St n8.mem SV n8 0x16BE (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = nl := by rw [u8.regs, g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by rw [u8.regs, g7_9]
  have g8_10 : reg n8 a0 = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 := by rw [u8.regs, g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = ni := by rw [u8.regs, g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by rw [u8.regs, g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = np := by rw [u8.regs, g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_18 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m8]; exact w7_18
  have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m8]; exact w7_24
  have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m8]; exact w7_28
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m8]; exact w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m8]; exact w7_34
  have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m8]; exact w7_38
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m8]; exact w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m8]; exact w7_48
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
  have b8_14 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m8]; exact b7_14
  have q8_1fc : ∀ j, j < 63 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m8]; exact q7_1fc j hj
  clear q7_1fc b7_14 w7_50 w7_48 w7_44 w7_38 w7_34 w7_30 w7_28 w7_24 w7_18 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x16BE
  obtain ⟨n9, c9, u9⟩ := s8.block svCns16be E8.self svCns16be_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0x16C8 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svCns16be (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_8 : reg n9 (8 : Fin 32) = nl := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by
    rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by
    rw [rb9, runBlock_reg _ _ _ (22 : Fin 32) s8.zero (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by
    rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = ni := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by
    rw [rb9, runBlock_reg _ _ _ (25 : Fin 32) s8.zero (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = np := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_10 : reg n9 a0 = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svCns16be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g9_11 : reg n9 a1 = (np) + ((ni) + BitVec.ofNat 32 0x1) := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svCns16be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g9_21 : reg n9 (21 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svCns16be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk9 : SvKeepL B n0.mem n9.mem [] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_18 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m9]; exact w8_18
  have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m9]; exact w8_24
  have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m9]; exact w8_28
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m9]; exact w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m9]; exact w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m9]; exact w8_38
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m9]; exact w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m9]; exact w8_48
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
  have b9_14 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m9]; exact b8_14
  have q9_1fc : ∀ j, j < 63 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m9]; exact q8_1fc j hj
  clear q8_1fc b8_14 w8_50 w8_48 w8_44 w8_38 w8_34 w8_30 w8_28 w8_24 w8_18 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0x16C8: sw
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_16c8 (off' := 0x16CA) (c := 0xC)
    (by decide) (by rw [g9_2]; sv_addr) (by decide) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = nl := by rw [rg10 (8 : Fin 32), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by rw [rg10 (9 : Fin 32), g9_9]
  have g10_10 : reg n10 a0 = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2 := by rw [rg10 a0, g9_10]
  have g10_11 : reg n10 a1 = (np) + ((ni) + BitVec.ofNat 32 0x1) := by rw [rg10 a1, g9_11]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rg10 (18 : Fin 32), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rg10 (19 : Fin 32), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [rg10 (20 : Fin 32), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg10 (21 : Fin 32), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [rg10 (22 : Fin 32), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [rg10 (23 : Fin 32), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = ni := by rw [rg10 (24 : Fin 32), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [rg10 (25 : Fin 32), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by rw [rg10 (26 : Fin 32), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = np := by rw [rg10 (27 : Fin 32), g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0xC, 0x4)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_18 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K10.w32 (by decide) (by decide)).trans w9_18
  have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K10.w32 (by decide) (by decide)).trans w9_24
  have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K10.w32 (by decide) (by decide)).trans w9_28
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K10.w32 (by decide) (by decide)).trans w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K10.w32 (by decide) (by decide)).trans w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K10.w32 (by decide) (by decide)).trans w9_38
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K10.w32 (by decide) (by decide)).trans w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K10.w32 (by decide) (by decide)).trans w9_48
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K10.w32 (by decide) (by decide)).trans w9_50
  have b10_14 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K10.b8 (by decide) (by decide)).trans b9_14
  have w10_c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2 := by rw [W10, g9_10]
  have q10_1fc : ∀ j, j < 63 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_1fc j hj)
  clear q9_1fc b9_14 w9_50 w9_48 w9_44 w9_38 w9_34 w9_30 w9_28 w9_24 w9_18 g9_21 g9_11 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x16CA
  obtain ⟨n11, c11, u11⟩ := s10.block svCns16ca E10.self svCns16ca_end
    ⟨trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0x16CC (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svCns16ca (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
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
  have g11_8 : reg n11 (8 : Fin 32) = nl := by
    rw [rb11, runBlock_reg _ _ _ (8 : Fin 32) s10.zero (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by
    rw [rb11, runBlock_reg _ _ _ (9 : Fin 32) s10.zero (by decide), g10_9]
  have g11_11 : reg n11 a1 = (np) + ((ni) + BitVec.ofNat 32 0x1) := by
    rw [rb11, runBlock_reg _ _ _ a1 s10.zero (by decide), g10_11]
  have g11_18 : reg n11 (18 : Fin 32) = out := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by
    rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = ni := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by
    rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = np := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_10 : reg n11 a0 = aluEval .sll (((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2) := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svCns16ca, upd, ↓reduceIte]; rw [g10_10] <;> rfl
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0xC, 0x4)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2 := by rw [m11]; exact w10_c
  have w11_18 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m11]; exact w10_18
  have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m11]; exact w10_24
  have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m11]; exact w10_28
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m11]; exact w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m11]; exact w10_34
  have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m11]; exact w10_38
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m11]; exact w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m11]; exact w10_48
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
  have b11_14 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m11]; exact b10_14
  have q11_1fc : ∀ j, j < 63 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m11]; exact q10_1fc j hj
  clear q10_1fc w10_c b10_14 w10_50 w10_48 w10_44 w10_38 w10_34 w10_30 w10_28 w10_24 w10_18 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_11 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0x16CC
  obtain ⟨n12, c12, u12⟩ := s11.block svCns16cc E11.self svCns16cc_end
    ⟨trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x16CE (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svCns16cc (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_8 : reg n12 (8 : Fin 32) = nl := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_11 : reg n12 a1 = (np) + ((ni) + BitVec.ofNat 32 0x1) := by
    rw [rb12, runBlock_reg _ _ _ a1 s11.zero (by decide), g11_11]
  have g12_18 : reg n12 (18 : Fin 32) = out := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by
    rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by
    rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = ni := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = np := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_10 : reg n12 a0 = (aluEval .sll (((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + ((np) + ((ni) + BitVec.ofNat 32 0x1)) := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svCns16cc, upd, ↓reduceIte]; rw [g11_10, g11_11] <;> rfl
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0xC, 0x4)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2 := by rw [m12]; exact w11_c
  have w12_18 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m12]; exact w11_18
  have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m12]; exact w11_24
  have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m12]; exact w11_28
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m12]; exact w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m12]; exact w11_34
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m12]; exact w11_38
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m12]; exact w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m12]; exact w11_48
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
  have b12_14 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m12]; exact b11_14
  have q12_1fc : ∀ j, j < 63 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m12]; exact q11_1fc j hj
  clear q11_1fc b11_14 w11_50 w11_48 w11_44 w11_38 w11_34 w11_30 w11_28 w11_24 w11_18 w11_c g11_10 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_11 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0x16CE: sw
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := sv_sw F E12 s12 sv_at_16ce (off' := 0x16D0) (c := 0x8)
    (by decide) (by rw [g12_2]; sv_addr) (by decide) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = nl := by rw [rg13 (8 : Fin 32), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by rw [rg13 (9 : Fin 32), g12_9]
  have g13_10 : reg n13 a0 = (aluEval .sll (((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + ((np) + ((ni) + BitVec.ofNat 32 0x1)) := by rw [rg13 a0, g12_10]
  have g13_11 : reg n13 a1 = (np) + ((ni) + BitVec.ofNat 32 0x1) := by rw [rg13 a1, g12_11]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rg13 (18 : Fin 32), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rg13 (19 : Fin 32), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [rg13 (20 : Fin 32), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg13 (21 : Fin 32), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [rg13 (22 : Fin 32), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [rg13 (23 : Fin 32), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = ni := by rw [rg13 (24 : Fin 32), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [rg13 (25 : Fin 32), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by rw [rg13 (26 : Fin 32), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = np := by rw [rg13 (27 : Fin 32), g12_27]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0xC, 0x4), (0x8, 0x4)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2 := (K13.w32 (by decide) (by decide)).trans w12_c
  have w13_18 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K13.w32 (by decide) (by decide)).trans w12_18
  have w13_24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K13.w32 (by decide) (by decide)).trans w12_24
  have w13_28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K13.w32 (by decide) (by decide)).trans w12_28
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K13.w32 (by decide) (by decide)).trans w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K13.w32 (by decide) (by decide)).trans w12_34
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K13.w32 (by decide) (by decide)).trans w12_38
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K13.w32 (by decide) (by decide)).trans w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K13.w32 (by decide) (by decide)).trans w12_48
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K13.w32 (by decide) (by decide)).trans w12_50
  have b13_14 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K13.b8 (by decide) (by decide)).trans b12_14
  have w13_8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = (aluEval .sll (((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + ((np) + ((ni) + BitVec.ofNat 32 0x1)) := by rw [W13, g12_10]
  have q13_1fc : ∀ j, j < 63 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K13.range (by decide) (by decide) j hj).trans (q12_1fc j hj)
  clear q12_1fc b12_14 w12_50 w12_48 w12_44 w12_38 w12_34 w12_30 w12_28 w12_24 w12_18 w12_c g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_11 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x16D0: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_16d0 (off' := 0x16D2) (c := 0x10)
    (by decide) (by rw [g13_2]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = nl := by rw [rg14 (8 : Fin 32), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by rw [rg14 (9 : Fin 32), g13_9]
  have g14_10 : reg n14 a0 = (aluEval .sll (((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + ((np) + ((ni) + BitVec.ofNat 32 0x1)) := by rw [rg14 a0, g13_10]
  have g14_11 : reg n14 a1 = (np) + ((ni) + BitVec.ofNat 32 0x1) := by rw [rg14 a1, g13_11]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [rg14 (20 : Fin 32), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [rg14 (23 : Fin 32), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = ni := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = np := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0xC, 0x4), (0x8, 0x4), (0x10, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = (aluEval .sll (((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + ((np) + ((ni) + BitVec.ofNat 32 0x1)) := (K14.w32 (by decide) (by decide)).trans w13_8
  have w14_c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2 := (K14.w32 (by decide) (by decide)).trans w13_c
  have w14_18 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K14.w32 (by decide) (by decide)).trans w13_18
  have w14_24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K14.w32 (by decide) (by decide)).trans w13_24
  have w14_28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K14.w32 (by decide) (by decide)).trans w13_28
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K14.w32 (by decide) (by decide)).trans w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K14.w32 (by decide) (by decide)).trans w13_34
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K14.w32 (by decide) (by decide)).trans w13_38
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K14.w32 (by decide) (by decide)).trans w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K14.w32 (by decide) (by decide)).trans w13_48
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K14.w32 (by decide) (by decide)).trans w13_50
  have b14_14 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K14.b8 (by decide) (by decide)).trans b13_14
  have w14_10 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = (np) + ((ni) + BitVec.ofNat 32 0x1) := by rw [W14, g13_11]
  have q14_1fc : ∀ j, j < 63 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_1fc j hj)
  clear q13_1fc w13_8 b13_14 w13_50 w13_48 w13_44 w13_38 w13_34 w13_30 w13_28 w13_24 w13_18 w13_c g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_11 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  -- 0x16D2
  obtain ⟨n15, c15, u15⟩ := s14.block svCns16d2 E14.self svCns16d2_end
    ⟨trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem SV n15 0x16D4 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock svCns16d2 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by
    rw [rb15, runBlock_reg _ _ _ sp s14.zero (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (3 : Fin 32) s14.zero (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (4 : Fin 32) s14.zero (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = nl := by
    rw [rb15, runBlock_reg _ _ _ (8 : Fin 32) s14.zero (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = (ni) + BitVec.ofNat 32 0x1 := by
    rw [rb15, runBlock_reg _ _ _ (9 : Fin 32) s14.zero (by decide), g14_9]
  have g15_11 : reg n15 a1 = (np) + ((ni) + BitVec.ofNat 32 0x1) := by
    rw [rb15, runBlock_reg _ _ _ a1 s14.zero (by decide), g14_11]
  have g15_18 : reg n15 (18 : Fin 32) = out := by
    rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by
    rw [rb15, runBlock_reg _ _ _ (19 : Fin 32) s14.zero (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by
    rw [rb15, runBlock_reg _ _ _ (20 : Fin 32) s14.zero (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb15, runBlock_reg _ _ _ (21 : Fin 32) s14.zero (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by
    rw [rb15, runBlock_reg _ _ _ (22 : Fin 32) s14.zero (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by
    rw [rb15, runBlock_reg _ _ _ (23 : Fin 32) s14.zero (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = ni := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by
    rw [rb15, runBlock_reg _ _ _ (25 : Fin 32) s14.zero (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = (nl) - ((ni) + BitVec.ofNat 32 0x1) := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = np := by
    rw [rb15, runBlock_reg _ _ _ (27 : Fin 32) s14.zero (by decide), g14_27]
  have g15_10 : reg n15 a0 = (np) + ((ni) + BitVec.ofNat 32 0x1) := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svCns16d2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_10, g14_11, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0xC, 0x4), (0x8, 0x4), (0x10, 0x4)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = (aluEval .sll (((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + ((np) + ((ni) + BitVec.ofNat 32 0x1)) := by rw [m15]; exact w14_8
  have w15_c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = ((nl) - ((ni) + BitVec.ofNat 32 0x1)) >>> 2 := by rw [m15]; exact w14_c
  have w15_10 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = (np) + ((ni) + BitVec.ofNat 32 0x1) := by rw [m15]; exact w14_10
  have w15_18 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m15]; exact w14_18
  have w15_24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m15]; exact w14_24
  have w15_28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m15]; exact w14_28
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m15]; exact w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m15]; exact w14_34
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m15]; exact w14_38
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m15]; exact w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m15]; exact w14_48
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m15]; exact w14_50
  have b15_14 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m15]; exact b14_14
  have q15_1fc : ∀ j, j < 63 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m15]; exact q14_1fc j hj
  clear q14_1fc w14_10 b14_14 w14_50 w14_48 w14_44 w14_38 w14_34 w14_30 w14_28 w14_24 w14_18 w14_c w14_8 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_11 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  exact .inr ⟨hc0, h4m, n15, t15, s15, E15, V15, fR15, g15_2, g15_3, g15_4, g15_8, g15_9, g15_10, g15_11, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, w15_8, w15_c, w15_10, w15_18, w15_24, w15_28, w15_30, w15_34, w15_38, w15_44, w15_48, w15_50, b15_14, q15_1fc, keep_kk15.mono (by decide)⟩

end C3.RV32.Sv
