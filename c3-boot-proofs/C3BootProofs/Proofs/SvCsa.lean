import C3BootProofs.Proofs.SvCs

/-!
# `sigstore::verify`: a signature line's em dash

From the signature loop's head at 0x1642 to the name scan at 0x1694: the signature section isn't empty, and its next line starts with an em dash and a space and goes on past them.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCsa1644 : List BInstr :=
  [.aluImm .and a0 a0 0x1]
theorem svCsa1644_end : blockEnd sigstoreVerifyCode 0x1644 svCsa1644 = some 0x1646 := by
  simp only [svCsa1644]
  rw [blockEnd, sv_at_1644]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCsa164e : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svCsa164e_end : blockEnd sigstoreVerifyCode 0x164E svCsa164e = some 0x1652 := by
  simp only [svCsa164e]
  rw [blockEnd, sv_at_164e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCsa1666 : List BInstr :=
  [.aluImm .add a3 sp 0x400]
theorem svCsa1666_end : blockEnd sigstoreVerifyCode 0x1666 svCsa1666 = some 0x166A := by
  simp only [svCsa1666]
  rw [blockEnd, sv_at_1666]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCsa1674 : List BInstr :=
  [.aluImm .add a3 x0 0x4, .lui a2 0x3FCC4000, .aluImm .add a2 a2 0x772]
theorem svCsa1674_end : blockEnd sigstoreVerifyCode 0x1674 svCsa1674 = some 0x167E := by
  simp only [svCsa1674]
  rw [blockEnd, sv_at_1674]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1676]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_167a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCsa1878 : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x1A]
theorem svCsa1878_end : blockEnd sigstoreVerifyCode 0x1878 svCsa1878 = some 0x187A := by
  simp only [svCsa1878]
  rw [blockEnd, sv_at_1878]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCsa168a : List BInstr :=
  [.alu .add (27 : Fin 32) x0 a0]
theorem svCsa168a_end : blockEnd sigstoreVerifyCode 0x168A svCsa168a = some 0x168C := by
  simp only [svCsa168a]
  rw [blockEnd, sv_at_168a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCsa168c : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a1]
theorem svCsa168c_end : blockEnd sigstoreVerifyCode 0x168C svCsa168c = some 0x168E := by
  simp only [svCsa168c]
  rw [blockEnd, sv_at_168c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCsa168e : List BInstr :=
  [.aluImm .add (24 : Fin 32) x0 0x0]
theorem svCsa168e_end : blockEnd sigstoreVerifyCode 0x168E svCsa168e = some 0x1690 := by
  simp only [svCsa168e]
  rw [blockEnd, sv_at_168e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_csa {B out bp x20 x21 x22 x23 x24 x25 x26 x27 f w38 w50 kh w48 w44 kp ckp bl : Word} {sg : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x1642 (reg n0))
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
    (hrem : w50 ≠ 0)
    (sg_in : SvIn B w38 w50.toNat)
    (CK0 : SvCkCode M0) :
    (¬ (∃ ix9, nlScan M0 (w38) 0 ((w50).toNat) = some ix9 ∧ (4 ≤ ix9 ∧ memBytes M0 w38 4 = memBytes M0 (BitVec.ofNat 32 (img% svDashAddress)) 4) ∧ (4 < ix9) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ ix9, nlScan M0 (w38) 0 ((w50).toNat) = some ix9 ∧
    (4 ≤ ix9 ∧ memBytes M0 w38 4 = memBytes M0 (BitVec.ofNat 32 (img% svDashAddress)) 4) ∧
    (4 < ix9) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1694 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (ix9 - 4) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = w38 + BitVec.ofNat 32 4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x1642: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_1642 (off' := 0x1644) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x30 = B + 0x21A0 + BitVec.ofNat 32 0x30 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0x1644 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
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
  have g1_10 : reg n1 a0 = f := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x30 = B + 0x21A0 + BitVec.ofNat 32 0x30 by sv_addr, w0_30]
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
  -- 0x1644
  obtain ⟨n2, c2, u2⟩ := s1.block svCsa1644 E1.self svCsa1644_end
    ⟨trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem SV n2 0x1646 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock svCsa1644 (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
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
  have g2_10 : reg n2 a0 = (f) &&& BitVec.ofNat 32 0x1 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svCsa1644, upd, ↓reduceIte]; rw [g1_10] <;> rfl
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
  clear q1_1fc b1_14 w1_50 w1_48 w1_44 w1_38 w1_34 w1_30 w1_28 w1_24 w1_18 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x1646: sw
  obtain ⟨n3, d3, s3, fr3, K3, W3, rg3⟩ := sv_sw F E2 s2 sv_at_1646 (off' := 0x1648) (c := 0x2C)
    (by decide) (by rw [g2_2]; sv_addr) (by decide) (by decide)
  have t3 : Steps n0 n3 := t2.trans d3
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.keep K3 (by decide)
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [rg3 sp, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg3 (3 : Fin 32), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg3 (4 : Fin 32), g2_4]
  have g3_10 : reg n3 a0 = (f) &&& BitVec.ofNat 32 0x1 := by rw [rg3 a0, g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [rg3 (18 : Fin 32), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [rg3 (19 : Fin 32), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [rg3 (20 : Fin 32), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [rg3 (21 : Fin 32), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [rg3 (22 : Fin 32), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [rg3 (23 : Fin 32), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [rg3 (24 : Fin 32), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [rg3 (25 : Fin 32), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [rg3 (26 : Fin 32), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [rg3 (27 : Fin 32), g2_27]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x2C, 0x4)] := keep_kk2.trans K3.toL
  clear keep_kk2
  have w3_18 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K3.w32 (by decide) (by decide)).trans w2_18
  have w3_24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K3.w32 (by decide) (by decide)).trans w2_24
  have w3_28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K3.w32 (by decide) (by decide)).trans w2_28
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K3.w32 (by decide) (by decide)).trans w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K3.w32 (by decide) (by decide)).trans w2_34
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K3.w32 (by decide) (by decide)).trans w2_38
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K3.w32 (by decide) (by decide)).trans w2_44
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K3.w32 (by decide) (by decide)).trans w2_48
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K3.w32 (by decide) (by decide)).trans w2_50
  have b3_14 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K3.b8 (by decide) (by decide)).trans b2_14
  have w3_2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [W3, g2_10]
  have q3_1fc : ∀ j, j < 63 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K3.range (by decide) (by decide) j hj).trans (q2_1fc j hj)
  clear q2_1fc b2_14 w2_50 w2_48 w2_44 w2_38 w2_34 w2_30 w2_28 w2_24 w2_18 g2_10 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0x1648: lw
  obtain ⟨n4, d4, u4⟩ := s3.lw E3.self sv_at_1648 (off' := 0x164A) (by decide)
    (by rw [g3_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s4 : St n4.mem SV n4 0x164A (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = x24 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = x27 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
  have g4_10 : reg n4 a0 = w50 := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w3_50]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x2C, 0x4)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_18 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m4]; exact w3_18
  have w4_24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m4]; exact w3_24
  have w4_28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m4]; exact w3_28
  have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m4]; exact w3_2c
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m4]; exact w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m4]; exact w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m4]; exact w3_38
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m4]; exact w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m4]; exact w3_48
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m4]; exact w3_50
  have b4_14 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m4]; exact b3_14
  have q4_1fc : ∀ j, j < 63 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m4]; exact q3_1fc j hj
  clear q3_1fc w3_2c b3_14 w3_50 w3_48 w3_44 w3_38 w3_34 w3_30 w3_28 w3_24 w3_18 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 rg3 W3 K3 fr3 s3 d3
  -- 0x164A: branch, not taken
  obtain ⟨n5, d5, u5⟩ := s4.notTaken E4.self 0x164E sv_at_164a
    (by decide) (by rw [g4_10, s4.zero]; exact br_beq_f hrem)
  have s5 : St n5.mem SV n5 0x164E (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
  have g5_10 : reg n5 a0 = w50 := by rw [u5.regs, g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [u5.regs, g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [u5.regs, g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x2C, 0x4)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_18 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m5]; exact w4_18
  have w5_24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m5]; exact w4_24
  have w5_28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m5]; exact w4_28
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m5]; exact w4_2c
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m5]; exact w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m5]; exact w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m5]; exact w4_38
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m5]; exact w4_48
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have b5_14 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m5]; exact b4_14
  have q5_1fc : ∀ j, j < 63 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_1fc j hj
  clear q4_1fc b4_14 w4_50 w4_48 w4_44 w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 w4_18 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0x164E
  obtain ⟨n6, c6, u6⟩ := s5.block svCsa164e E5.self svCsa164e_end
    ⟨trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x1652 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svCsa164e (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svCsa164e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_10, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x2C, 0x4)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_18 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m6]; exact w5_18
  have w6_24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m6]; exact w5_24
  have w6_28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m6]; exact w5_28
  have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m6]; exact w5_2c
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m6]; exact w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m6]; exact w5_34
  have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m6]; exact w5_38
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m6]; exact w5_48
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
  have b6_14 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m6]; exact b5_14
  have q6_1fc : ∀ j, j < 63 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_1fc j hj
  clear q5_1fc b5_14 w5_50 w5_48 w5_44 w5_38 w5_34 w5_30 w5_2c w5_28 w5_24 w5_18 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x1652: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_1652 (off' := 0x1654) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0x1654 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_10]
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
  have g7_11 : reg n7 a1 = w38 := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr, w6_38]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x2C, 0x4)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_18 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m7]; exact w6_18
  have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m7]; exact w6_24
  have w7_28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m7]; exact w6_28
  have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m7]; exact w6_2c
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m7]; exact w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m7]; exact w6_34
  have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m7]; exact w6_38
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m7]; exact w6_44
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m7]; exact w6_48
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
  have b7_14 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m7]; exact b6_14
  have q7_1fc : ∀ j, j < 63 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m7]; exact q6_1fc j hj
  clear q6_1fc b6_14 w6_50 w6_48 w6_44 w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 w6_18 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0x1654: lw
  obtain ⟨n8, d8, u8⟩ := s7.lw E7.self sv_at_1654 (off' := 0x1656) (by decide)
    (by rw [g7_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s8 : St n8.mem SV n8 0x1656 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_10]
  have g8_11 : reg n8 a1 = w38 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_11]
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
  have g8_12 : reg n8 a2 = w50 := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w7_50]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x2C, 0x4)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_18 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m8]; exact w7_18
  have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m8]; exact w7_24
  have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m8]; exact w7_28
  have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m8]; exact w7_2c
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m8]; exact w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m8]; exact w7_34
  have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m8]; exact w7_38
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m8]; exact w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m8]; exact w7_48
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
  have b8_14 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m8]; exact b7_14
  have q8_1fc : ∀ j, j < 63 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m8]; exact q7_1fc j hj
  clear q7_1fc b7_14 w7_50 w7_48 w7_44 w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 w7_18 g7_11 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x1656: sv_lineF
  obtain ⟨n9, c9, s9, rk9, K9, L9, fr9⟩ := sv_lineF (oc := 0x420) (nl := (w50).toNat)
    F E8 (CK0.sv FW fR8) s8 sv_at_1656 sv_at_165a (by decide) (by decide)
    g8_10 g8_11 (by rw [g8_12, ofNat_toNat_self]) (by decide) (by decide) (.inl sg_in)
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keepL K9 (by decide)
  rw [nlScan_ro FW fR8 (.inl sg_in)] at L9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rk9 sp (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk9 (3 : Fin 32) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk9 (4 : Fin 32) (by decide), g8_4]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rk9 (18 : Fin 32) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rk9 (19 : Fin 32) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [rk9 (20 : Fin 32) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [rk9 (21 : Fin 32) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [rk9 (22 : Fin 32) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [rk9 (23 : Fin 32) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [rk9 (24 : Fin 32) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [rk9 (25 : Fin 32) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [rk9 (26 : Fin 32) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [rk9 (27 : Fin 32) (by decide), g8_27]
  obtain ⟨r9, hr9⟩ : ∃ r, nlScan M0 (w38) 0 ((w50).toNat) = r := ⟨_, rfl⟩
  rcases r9 with _ | ix9
  · rw [hr9] at L9
    obtain ⟨z0_9, z4_9⟩ := L9
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x2C, 0x4), (0x420, 0x10)] := keep_kk8.trans K9
    clear keep_kk8
    have w9_18 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K9.w32 (by decide) (by decide)).trans w8_18
    have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K9.w32 (by decide) (by decide)).trans w8_24
    have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K9.w32 (by decide) (by decide)).trans w8_28
    have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := (K9.w32 (by decide) (by decide)).trans w8_2c
    have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K9.w32 (by decide) (by decide)).trans w8_30
    have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K9.w32 (by decide) (by decide)).trans w8_34
    have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K9.w32 (by decide) (by decide)).trans w8_38
    have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K9.w32 (by decide) (by decide)).trans w8_44
    have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K9.w32 (by decide) (by decide)).trans w8_48
    have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K9.w32 (by decide) (by decide)).trans w8_50
    have b9_14 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K9.b8 (by decide) (by decide)).trans b8_14
    have q9_1fc : ∀ j, j < 63 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_1fc j hj)
    have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z0_9
    have b9_424 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := z4_9
    clear q8_1fc b8_14 w8_50 w8_48 w8_44 w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 w8_18 g8_12 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_11 g8_10 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    -- 0x165E: lw
    obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_165e (off' := 0x1662) (by decide)
      (by rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s10 : St n10.mem SV n10 0x1662 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
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
    have g10_10 : reg n10 a0 = 0 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w9_420]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x2C, 0x4), (0x420, 0x10)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_18 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m10]; exact w9_18
    have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m10]; exact w9_24
    have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m10]; exact w9_28
    have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m10]; exact w9_2c
    have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m10]; exact w9_30
    have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m10]; exact w9_34
    have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m10]; exact w9_38
    have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
    have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m10]; exact w9_48
    have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
    have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m10]; exact w9_420
    have b10_14 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m10]; exact b9_14
    have b10_424 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m10]; exact b9_424
    have q10_1fc : ∀ j, j < 63 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_1fc j hj
    clear b9_424 w9_420 q9_1fc b9_14 w9_50 w9_48 w9_44 w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 w9_18 z4_9 z0_9
    -- 0x1662: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x1872 sv_at_1662
      (by decide) (by rw [g10_10, s10.zero]; rfl)
    have s11 : St n11.mem SV n11 0x1872 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_10 : reg n11 a0 = 0 := by rw [u11.regs, g10_10]
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
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x2C, 0x4), (0x420, 0x10)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_18 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m11]; exact w10_18
    have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m11]; exact w10_24
    have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m11]; exact w10_28
    have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m11]; exact w10_2c
    have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m11]; exact w10_30
    have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m11]; exact w10_34
    have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m11]; exact w10_38
    have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m11]; exact w10_44
    have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m11]; exact w10_48
    have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m11]; exact w10_420
    have b11_14 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m11]; exact b10_14
    have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m11]; exact b10_424
    have q11_1fc : ∀ j, j < 63 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m11]; exact q10_1fc j hj
    clear q10_1fc b10_424 b10_14 w10_420 w10_50 w10_48 w10_44 w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 w10_18 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x1872: lbu
    obtain ⟨n12, d12, u12⟩ := s11.lbu E11.self sv_at_1872 (off' := 0x1876) (by decide)
    have s12 : St n12.mem SV n12 0x1876 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
    have g12_10 : reg n12 a0 = 0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_10]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x2C, 0x4), (0x420, 0x10)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_18 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m12]; exact w11_18
    have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m12]; exact w11_24
    have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m12]; exact w11_28
    have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m12]; exact w11_2c
    have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m12]; exact w11_30
    have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m12]; exact w11_34
    have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m12]; exact w11_38
    have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m12]; exact w11_44
    have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m12]; exact w11_48
    have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m12]; exact w11_420
    have b12_14 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m12]; exact b11_14
    have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m12]; exact b11_424
    have q12_1fc : ∀ j, j < 63 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m12]; exact q11_1fc j hj
    clear q11_1fc b11_424 b11_14 w11_420 w11_50 w11_48 w11_44 w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 w11_18 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    -- 0x1876: j
    obtain ⟨n13, d13, u13⟩ := s12.jump E12.self sv_at_1876 (off' := 0x1882) (by decide)
      (by rw [s12.pc]; decide)
    have s13 : St n13.mem SV n13 0x1882 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
    have t13 : Steps n0 n13 := t12.trans (.single d13)
    have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
    have E13 : SvCode n13.mem := E12.fr F fr13
    have V13 : SvSaves B n13.mem v := V12.same m13
    have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
    have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
    have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
    have g13_10 : reg n13 a0 = 0 := by rw [u13.regs, g12_10]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, g12_24]
    have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, g12_27]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x2C, 0x4), (0x420, 0x10)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_18 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m13]; exact w12_18
    have w13_24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m13]; exact w12_24
    have w13_28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m13]; exact w12_28
    have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m13]; exact w12_2c
    have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m13]; exact w12_30
    have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m13]; exact w12_34
    have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m13]; exact w12_38
    have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m13]; exact w12_44
    have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m13]; exact w12_48
    have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m13]; exact w12_420
    have b13_14 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m13]; exact b12_14
    have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m13]; exact b12_424
    have q13_1fc : ∀ j, j < 63 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m13]; exact q12_1fc j hj
    clear q12_1fc b12_424 b12_14 w12_420 w12_50 w12_48 w12_44 w12_38 w12_34 w12_30 w12_2c w12_28 w12_24 w12_18 g12_27 g12_26 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    exact .inl ⟨(fun ⟨ix9', h0', _⟩ => by rw [hr9] at h0'; cases h0'), sv_fail_1882 F E13 s13 t13 (fun x hx => (fR13 x hx).trans (fM x hx).symm) V13 hret g13_2 g13_18 hO g13_3 g13_4⟩
  have hix9 : ix9 < (w50).toNat := by have := (nlScan_lt _ _ _ hr9).2; omega
  rw [hr9] at L9
  obtain ⟨y0_9, y4_9, y8_9, y12_9⟩ := L9
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x2C, 0x4), (0x420, 0x10)] := keep_kk8.trans K9
  clear keep_kk8
  have w9_18 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K9.w32 (by decide) (by decide)).trans w8_18
  have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K9.w32 (by decide) (by decide)).trans w8_24
  have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K9.w32 (by decide) (by decide)).trans w8_28
  have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := (K9.w32 (by decide) (by decide)).trans w8_2c
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K9.w32 (by decide) (by decide)).trans w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K9.w32 (by decide) (by decide)).trans w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K9.w32 (by decide) (by decide)).trans w8_38
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K9.w32 (by decide) (by decide)).trans w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K9.w32 (by decide) (by decide)).trans w8_48
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K9.w32 (by decide) (by decide)).trans w8_50
  have b9_14 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K9.b8 (by decide) (by decide)).trans b8_14
  have q9_1fc : ∀ j, j < 63 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_1fc j hj)
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := y0_9
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := y4_9
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := y8_9
  have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := y12_9
  clear q8_1fc b8_14 w8_50 w8_48 w8_44 w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 w8_18 g8_12 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_11 g8_10 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0x165E: lw
  obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_165e (off' := 0x1662) (by decide)
    (by rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s10 : St n10.mem SV n10 0x1662 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
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
  have g10_10 : reg n10 a0 = w38 := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w9_420]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x2C, 0x4), (0x420, 0x10)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_18 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m10]; exact w9_18
  have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m10]; exact w9_24
  have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m10]; exact w9_28
  have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m10]; exact w9_2c
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m10]; exact w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m10]; exact w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m10]; exact w9_38
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m10]; exact w9_48
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m10]; exact w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m10]; exact w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m10]; exact w9_428
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m10]; exact w9_42c
  have b10_14 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m10]; exact b9_14
  have q10_1fc : ∀ j, j < 63 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_1fc j hj
  clear w9_42c w9_428 w9_424 w9_420 q9_1fc b9_14 w9_50 w9_48 w9_44 w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 w9_18 y12_9 y8_9 y4_9 y0_9 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 K9 rk9 s9 c9
  -- 0x1662: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0x1666 sv_at_1662
    (by decide) (by rw [g10_10, s10.zero]; exact br_beq_f sg_in.pos_ne)
  have s11 : St n11.mem SV n11 0x1666 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_10 : reg n11 a0 = w38 := by rw [u11.regs, g10_10]
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
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x2C, 0x4), (0x420, 0x10)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_18 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m11]; exact w10_18
  have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m11]; exact w10_24
  have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m11]; exact w10_28
  have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m11]; exact w10_2c
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m11]; exact w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m11]; exact w10_34
  have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m11]; exact w10_38
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m11]; exact w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m11]; exact w10_48
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m11]; exact w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m11]; exact w10_42c
  have b11_14 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m11]; exact b10_14
  have q11_1fc : ∀ j, j < 63 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m11]; exact q10_1fc j hj
  clear q10_1fc b10_14 w10_42c w10_428 w10_424 w10_420 w10_50 w10_48 w10_44 w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 w10_18 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x1666
  obtain ⟨n12, c12, u12⟩ := s11.block svCsa1666 E11.self svCsa1666_end
    ⟨trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x166A (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svCsa1666 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_10 : reg n12 a0 = w38 := by
    rw [rb12, runBlock_reg _ _ _ a0 s11.zero (by decide), g11_10]
  have g12_18 : reg n12 (18 : Fin 32) = out := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by
    rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by
    rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_13 : reg n12 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svCsa1666, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x2C, 0x4), (0x420, 0x10)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_18 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m12]; exact w11_18
  have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m12]; exact w11_24
  have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m12]; exact w11_28
  have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m12]; exact w11_2c
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m12]; exact w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m12]; exact w11_34
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m12]; exact w11_38
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m12]; exact w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m12]; exact w11_48
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m12]; exact w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m12]; exact w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m12]; exact w11_42c
  have b12_14 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m12]; exact b11_14
  have q12_1fc : ∀ j, j < 63 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m12]; exact q11_1fc j hj
  clear q11_1fc b11_14 w11_42c w11_428 w11_424 w11_420 w11_50 w11_48 w11_44 w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 w11_18 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x166A: lw
  obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_166a (off' := 0x166C) (by decide)
    (by rw [g12_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s13 : St n13.mem SV n13 0x166C (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_10 : reg n13 a0 = w38 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_10]
  have g13_13 : reg n13 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_13]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 ix9 := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w12_424]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x2C, 0x4), (0x420, 0x10)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_18 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m13]; exact w12_18
  have w13_24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m13]; exact w12_24
  have w13_28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m13]; exact w12_28
  have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m13]; exact w12_2c
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m13]; exact w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m13]; exact w12_34
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m13]; exact w12_38
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m13]; exact w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m13]; exact w12_48
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m13]; exact w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m13]; exact w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m13]; exact w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m13]; exact w12_42c
  have b13_14 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m13]; exact b12_14
  have q13_1fc : ∀ j, j < 63 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m13]; exact q12_1fc j hj
  clear q12_1fc b12_14 w12_42c w12_428 w12_424 w12_420 w12_50 w12_48 w12_44 w12_38 w12_34 w12_30 w12_2c w12_28 w12_24 w12_18 g12_13 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x166C: lw
  obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_166c (off' := 0x166E) (by decide)
    (by rw [g13_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s14 : St n14.mem SV n14 0x166E (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
  have g14_10 : reg n14 a0 = w38 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_10]
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 ix9 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_11]
  have g14_13 : reg n14 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_13]
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
  have g14_12 : reg n14 a2 = (w38) + BitVec.ofNat 32 (ix9 + 1) := by
    rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g13_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w13_428]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x2C, 0x4), (0x420, 0x10)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_18 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m14]; exact w13_18
  have w14_24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m14]; exact w13_24
  have w14_28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m14]; exact w13_28
  have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m14]; exact w13_2c
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m14]; exact w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m14]; exact w13_34
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m14]; exact w13_38
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m14]; exact w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m14]; exact w13_48
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m14]; exact w13_50
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m14]; exact w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m14]; exact w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m14]; exact w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m14]; exact w13_42c
  have b14_14 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m14]; exact b13_14
  have q14_1fc : ∀ j, j < 63 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m14]; exact q13_1fc j hj
  clear q13_1fc b13_14 w13_42c w13_428 w13_424 w13_420 w13_50 w13_48 w13_44 w13_38 w13_34 w13_30 w13_2c w13_28 w13_24 w13_18 g13_11 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_13 g13_10 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0x166E: sw
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sw F E14 s14 sv_at_166e (off' := 0x1670) (c := 0x38)
    (by decide) (by rw [g14_2]; sv_addr) (by decide) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_10 : reg n15 a0 = w38 := by rw [rg15 a0, g14_10]
  have g15_11 : reg n15 a1 = BitVec.ofNat 32 ix9 := by rw [rg15 a1, g14_11]
  have g15_12 : reg n15 a2 = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [rg15 a2, g14_12]
  have g15_13 : reg n15 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg15 a3, g14_13]
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
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_18 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K15.w32 (by decide) (by decide)).trans w14_18
  have w15_24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K15.w32 (by decide) (by decide)).trans w14_24
  have w15_28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K15.w32 (by decide) (by decide)).trans w14_28
  have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := (K15.w32 (by decide) (by decide)).trans w14_2c
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K15.w32 (by decide) (by decide)).trans w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K15.w32 (by decide) (by decide)).trans w14_34
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K15.w32 (by decide) (by decide)).trans w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K15.w32 (by decide) (by decide)).trans w14_48
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K15.w32 (by decide) (by decide)).trans w14_50
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := (K15.w32 (by decide) (by decide)).trans w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := (K15.w32 (by decide) (by decide)).trans w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := (K15.w32 (by decide) (by decide)).trans w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := (K15.w32 (by decide) (by decide)).trans w14_42c
  have b15_14 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K15.b8 (by decide) (by decide)).trans b14_14
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [W15, g14_12]
  have q15_1fc : ∀ j, j < 63 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_1fc j hj)
  clear q14_1fc b14_14 w14_42c w14_428 w14_424 w14_420 w14_50 w14_48 w14_44 w14_38 w14_34 w14_30 w14_2c w14_28 w14_24 w14_18 g14_12 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_13 g14_11 g14_10 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0x1670: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_1670 (off' := 0x1672) (by decide)
    (by rw [g15_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s16 : St n16.mem SV n16 0x1672 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_10 : reg n16 a0 = w38 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_10]
  have g16_11 : reg n16 a1 = BitVec.ofNat 32 ix9 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_11]
  have g16_13 : reg n16 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_13]
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
  have g16_12 : reg n16 a2 = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w15_42c]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_18 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m16]; exact w15_18
  have w16_24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m16]; exact w15_24
  have w16_28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m16]; exact w15_28
  have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m16]; exact w15_2c
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m16]; exact w15_30
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m16]; exact w15_34
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m16]; exact w15_38
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m16]; exact w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m16]; exact w15_48
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m16]; exact w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m16]; exact w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m16]; exact w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m16]; exact w15_42c
  have b16_14 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m16]; exact b15_14
  have q16_1fc : ∀ j, j < 63 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m16]; exact q15_1fc j hj
  clear q15_1fc w15_38 b15_14 w15_42c w15_428 w15_424 w15_420 w15_50 w15_48 w15_44 w15_34 w15_30 w15_2c w15_28 w15_24 w15_18 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_13 g15_12 g15_11 g15_10 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  -- 0x1672: sw
  obtain ⟨n17, d17, s17, fr17, K17, W17, rg17⟩ := sv_sw F E16 s16 sv_at_1672 (off' := 0x1674) (c := 0x50)
    (by decide) (by rw [g16_2]; sv_addr) (by decide) (by decide)
  have t17 : Steps n0 n17 := t16.trans d17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rg17 sp, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg17 (3 : Fin 32), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg17 (4 : Fin 32), g16_4]
  have g17_10 : reg n17 a0 = w38 := by rw [rg17 a0, g16_10]
  have g17_11 : reg n17 a1 = BitVec.ofNat 32 ix9 := by rw [rg17 a1, g16_11]
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [rg17 a2, g16_12]
  have g17_13 : reg n17 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg17 a3, g16_13]
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
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_18 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K17.w32 (by decide) (by decide)).trans w16_18
  have w17_24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K17.w32 (by decide) (by decide)).trans w16_24
  have w17_28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K17.w32 (by decide) (by decide)).trans w16_28
  have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := (K17.w32 (by decide) (by decide)).trans w16_2c
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K17.w32 (by decide) (by decide)).trans w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K17.w32 (by decide) (by decide)).trans w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := (K17.w32 (by decide) (by decide)).trans w16_38
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K17.w32 (by decide) (by decide)).trans w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K17.w32 (by decide) (by decide)).trans w16_48
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := (K17.w32 (by decide) (by decide)).trans w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := (K17.w32 (by decide) (by decide)).trans w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := (K17.w32 (by decide) (by decide)).trans w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := (K17.w32 (by decide) (by decide)).trans w16_42c
  have b17_14 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K17.b8 (by decide) (by decide)).trans b16_14
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [W17, g16_12]
  have q17_1fc : ∀ j, j < 63 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K17.range (by decide) (by decide) j hj).trans (q16_1fc j hj)
  clear q16_1fc b16_14 w16_42c w16_428 w16_424 w16_420 w16_50 w16_48 w16_44 w16_38 w16_34 w16_30 w16_2c w16_28 w16_24 w16_18 g16_12 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_13 g16_11 g16_10 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0x1674
  obtain ⟨n18, c18, u18⟩ := s17.block svCsa1674 E17.self svCsa1674_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem SV n18 0x167E (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock svCsa1674 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
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
  have g18_10 : reg n18 a0 = w38 := by
    rw [rb18, runBlock_reg _ _ _ a0 s17.zero (by decide), g17_10]
  have g18_11 : reg n18 a1 = BitVec.ofNat 32 ix9 := by
    rw [rb18, runBlock_reg _ _ _ a1 s17.zero (by decide), g17_11]
  have g18_18 : reg n18 (18 : Fin 32) = out := by
    rw [rb18, runBlock_reg _ _ _ (18 : Fin 32) s17.zero (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by
    rw [rb18, runBlock_reg _ _ _ (19 : Fin 32) s17.zero (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by
    rw [rb18, runBlock_reg _ _ _ (20 : Fin 32) s17.zero (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by
    rw [rb18, runBlock_reg _ _ _ (21 : Fin 32) s17.zero (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by
    rw [rb18, runBlock_reg _ _ _ (22 : Fin 32) s17.zero (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by
    rw [rb18, runBlock_reg _ _ _ (23 : Fin 32) s17.zero (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by
    rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by
    rw [rb18, runBlock_reg _ _ _ (25 : Fin 32) s17.zero (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by
    rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by
    rw [rb18, runBlock_reg _ _ _ (27 : Fin 32) s17.zero (by decide), g17_27]
  have g18_12 : reg n18 a2 = BitVec.ofNat 32 (img% svDashAddress) := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svCsa1674, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_10, g17_11, g17_12, g17_13, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_13 : reg n18 a3 = BitVec.ofNat 32 0x4 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svCsa1674, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_10, g17_11, g17_12, g17_13, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_18 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m18]; exact w17_18
  have w18_24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m18]; exact w17_24
  have w18_28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m18]; exact w17_28
  have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m18]; exact w17_2c
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m18]; exact w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m18]; exact w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m18]; exact w17_38
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m18]; exact w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m18]; exact w17_48
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m18]; exact w17_50
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m18]; exact w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m18]; exact w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m18]; exact w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m18]; exact w17_42c
  have b18_14 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m18]; exact b17_14
  have q18_1fc : ∀ j, j < 63 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m18]; exact q17_1fc j hj
  clear q17_1fc w17_50 b17_14 w17_42c w17_428 w17_424 w17_420 w17_48 w17_44 w17_38 w17_34 w17_30 w17_2c w17_28 w17_24 w17_18 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_13 g17_12 g17_11 g17_10 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
  -- 0x167E: sv_spfF
  obtain ⟨n19, c19, s19, rk19, a0_19, a1_19, K19, fr19⟩ := sv_spfF (sl := ix9) (pl := 4)
    F E18 (CK0.sv FW fR18) s18 sv_at_167e sv_at_1682 (by decide) (by decide) g18_2
    g18_10 g18_11 g18_12 g18_13 (.inl (sg_in.shrink (Nat.le_of_lt hix9))) (.inr ⟨by decide, by decide⟩)
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keepL K19 (by decide)
  rw [spf_ite FW fR18 (.inl (sg_in.shrink (Nat.le_of_lt hix9))), sv_mbRo (q := BitVec.ofNat 32 (img% svDashAddress)) (ql := 4) FW fR18 (.inr ⟨by decide, by decide⟩)] at a0_19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [rk19 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk19 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk19 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_4]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rk19 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rk19 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [rk19 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [rk19 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [rk19 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [rk19 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [rk19 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [rk19 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [rk19 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [rk19 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g18_27]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := keep_kk18.trans K19
  clear keep_kk18
  have w19_18 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K19.w32 (by decide) (by decide)).trans w18_18
  have w19_24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K19.w32 (by decide) (by decide)).trans w18_24
  have w19_28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K19.w32 (by decide) (by decide)).trans w18_28
  have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := (K19.w32 (by decide) (by decide)).trans w18_2c
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K19.w32 (by decide) (by decide)).trans w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K19.w32 (by decide) (by decide)).trans w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := (K19.w32 (by decide) (by decide)).trans w18_38
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K19.w32 (by decide) (by decide)).trans w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K19.w32 (by decide) (by decide)).trans w18_48
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := (K19.w32 (by decide) (by decide)).trans w18_50
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := (K19.w32 (by decide) (by decide)).trans w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := (K19.w32 (by decide) (by decide)).trans w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := (K19.w32 (by decide) (by decide)).trans w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := (K19.w32 (by decide) (by decide)).trans w18_42c
  have b19_14 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K19.b8 (by decide) (by decide)).trans b18_14
  have q19_1fc : ∀ j, j < 63 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K19.range (by decide) (by decide) j hj).trans (q18_1fc j hj)
  clear q18_1fc b18_14 w18_42c w18_428 w18_424 w18_420 w18_50 w18_48 w18_44 w18_38 w18_34 w18_30 w18_2c w18_28 w18_24 w18_18 g18_13 g18_12 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_11 g18_10 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  by_cases hdash : 4 ≤ ix9 ∧ memBytes M0 w38 4 = memBytes M0 (BitVec.ofNat 32 (img% svDashAddress)) 4
  rotate_left
  · have g19_10 : reg n19 a0 = BitVec.ofNat 32 0x0 := by rw [a0_19, if_neg hdash]; rfl
    -- 0x1686: branch, taken
    obtain ⟨n20, d20, u20⟩ := s19.taken E19.self 0x1878 sv_at_1686
      (by decide) (by rw [g19_10, s19.zero]; decide)
    have s20 : St n20.mem SV n20 0x1878 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
    have t20 : Steps n0 n20 := t19.trans (.single d20)
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.same m20
    have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, g19_4]
    have g20_10 : reg n20 a0 = BitVec.ofNat 32 0x0 := by rw [u20.regs, g19_10]
    have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, g19_19]
    have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, g19_20]
    have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [u20.regs, g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = x24 := by rw [u20.regs, g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [u20.regs, g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [u20.regs, g19_27]
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_18 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m20]; exact w19_18
    have w20_24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m20]; exact w19_24
    have w20_28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m20]; exact w19_28
    have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m20]; exact w19_2c
    have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m20]; exact w19_30
    have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m20]; exact w19_34
    have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m20]; exact w19_38
    have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m20]; exact w19_44
    have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m20]; exact w19_48
    have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m20]; exact w19_50
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m20]; exact w19_420
    have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m20]; exact w19_424
    have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m20]; exact w19_428
    have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m20]; exact w19_42c
    have b20_14 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m20]; exact b19_14
    have q20_1fc : ∀ j, j < 63 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m20]; exact q19_1fc j hj
    clear q19_1fc b19_14 w19_42c w19_428 w19_424 w19_420 w19_50 w19_48 w19_44 w19_38 w19_34 w19_30 w19_2c w19_28 w19_24 w19_18 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 K19 a1_19 a0_19 rk19 s19 c19
    -- 0x1878
    obtain ⟨n21, c21, u21⟩ := s20.block svCsa1878 E20.self svCsa1878_end
      ⟨trivial, trivial⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have s21 : St n21.mem SV n21 0x187A (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have rb21 : ∀ q, reg n21 q = (runBlock svCsa1878 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
    have g21_10 : reg n21 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb21, runBlock_reg _ _ _ a0 s20.zero (by decide), g20_10]
    have g21_18 : reg n21 (18 : Fin 32) = out := by
      rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by
      rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = x20 := by
      rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by
      rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = x22 := by
      rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = x23 := by
      rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = x24 := by
      rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by
      rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = x27 := by
      rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
    have g21_25 : reg n21 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb21]; simp +decide only [runBlock, BInstr.run, svCsa1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g20_2, g20_3, g20_4, g20_10, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_18 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m21]; exact w20_18
    have w21_24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m21]; exact w20_24
    have w21_28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m21]; exact w20_28
    have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m21]; exact w20_2c
    have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m21]; exact w20_30
    have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m21]; exact w20_34
    have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m21]; exact w20_38
    have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m21]; exact w20_44
    have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m21]; exact w20_48
    have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m21]; exact w20_50
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m21]; exact w20_420
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m21]; exact w20_424
    have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m21]; exact w20_428
    have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m21]; exact w20_42c
    have b21_14 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m21]; exact b20_14
    have q21_1fc : ∀ j, j < 63 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m21]; exact q20_1fc j hj
    clear q20_1fc b20_14 w20_42c w20_428 w20_424 w20_420 w20_50 w20_48 w20_44 w20_38 w20_34 w20_30 w20_2c w20_28 w20_24 w20_18 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20 g19_10
    -- 0x187A: j
    obtain ⟨n22, d22, u22⟩ := s21.jump E21.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s21.pc]; decide)
    have s22 : St n22.mem SV n22 0x1882 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
    have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_10]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = x24 := by rw [u22.regs, g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u22.regs, g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_18 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m22]; exact w21_18
    have w22_24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m22]; exact w21_24
    have w22_28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m22]; exact w21_28
    have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m22]; exact w21_2c
    have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m22]; exact w21_30
    have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m22]; exact w21_34
    have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m22]; exact w21_38
    have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m22]; exact w21_44
    have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m22]; exact w21_48
    have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m22]; exact w21_50
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m22]; exact w21_420
    have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m22]; exact w21_424
    have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m22]; exact w21_428
    have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m22]; exact w21_42c
    have b22_14 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m22]; exact b21_14
    have q22_1fc : ∀ j, j < 63 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m22]; exact q21_1fc j hj
    clear q21_1fc b21_14 w21_42c w21_428 w21_424 w21_420 w21_50 w21_48 w21_44 w21_38 w21_34 w21_30 w21_2c w21_28 w21_24 w21_18 g21_25 g21_27 g21_26 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_10 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
    exact .inl ⟨(fun ⟨ix9', h0', h1', _⟩ => by rw [hr9] at h0'; cases h0'; exact hdash h1'), sv_fail_1882 F E22 s22 t22 (fun x hx => (fR22 x hx).trans (fM x hx).symm) V22 hret g22_2 g22_18 hO g22_3 g22_4⟩
  have g19_10 : reg n19 a0 = w38 + BitVec.ofNat 32 4 := by rw [a0_19, if_pos hdash]
  have g19_11 : reg n19 a1 = BitVec.ofNat 32 (ix9 - 4) := a1_19 hdash.1
  -- 0x1686: branch, not taken
  obtain ⟨n20, d20, u20⟩ := s19.notTaken E19.self 0x168A sv_at_1686
    (by decide) (by rw [g19_10, s19.zero]; exact br_beq_f ((sg_in.shrink (Nat.le_of_lt hix9)).drop hdash.1).pos_ne)
  have s20 : St n20.mem SV n20 0x168A (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, g19_4]
  have g20_10 : reg n20 a0 = w38 + BitVec.ofNat 32 4 := by rw [u20.regs, g19_10]
  have g20_11 : reg n20 a1 = BitVec.ofNat 32 (ix9 - 4) := by rw [u20.regs, g19_11]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [u20.regs, g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = x24 := by rw [u20.regs, g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [u20.regs, g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [u20.regs, g19_27]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_18 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m20]; exact w19_18
  have w20_24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m20]; exact w19_24
  have w20_28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m20]; exact w19_28
  have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m20]; exact w19_2c
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m20]; exact w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m20]; exact w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m20]; exact w19_38
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m20]; exact w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m20]; exact w19_48
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m20]; exact w19_50
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m20]; exact w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m20]; exact w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m20]; exact w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m20]; exact w19_42c
  have b20_14 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m20]; exact b19_14
  have q20_1fc : ∀ j, j < 63 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m20]; exact q19_1fc j hj
  clear q19_1fc b19_14 w19_42c w19_428 w19_424 w19_420 w19_50 w19_48 w19_44 w19_38 w19_34 w19_30 w19_2c w19_28 w19_24 w19_18 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 K19 a1_19 a0_19 rk19 s19 c19
  -- 0x168A
  obtain ⟨n21, c21, u21⟩ := s20.block svCsa168a E20.self svCsa168a_end
    ⟨trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x168C (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svCsa168a (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
  have g21_10 : reg n21 a0 = w38 + BitVec.ofNat 32 4 := by
    rw [rb21, runBlock_reg _ _ _ a0 s20.zero (by decide), g20_10]
  have g21_11 : reg n21 a1 = BitVec.ofNat 32 (ix9 - 4) := by
    rw [rb21, runBlock_reg _ _ _ a1 s20.zero (by decide), g20_11]
  have g21_18 : reg n21 (18 : Fin 32) = out := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by
    rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by
    rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = w38 + BitVec.ofNat 32 4 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svCsa168a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_10, g20_11, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_18 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m21]; exact w20_18
  have w21_24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m21]; exact w20_24
  have w21_28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m21]; exact w20_28
  have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m21]; exact w20_2c
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m21]; exact w20_30
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m21]; exact w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m21]; exact w20_38
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m21]; exact w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m21]; exact w20_48
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m21]; exact w20_50
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m21]; exact w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m21]; exact w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m21]; exact w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m21]; exact w20_42c
  have b21_14 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m21]; exact b20_14
  have q21_1fc : ∀ j, j < 63 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m21]; exact q20_1fc j hj
  clear q20_1fc b20_14 w20_42c w20_428 w20_424 w20_420 w20_50 w20_48 w20_44 w20_38 w20_34 w20_30 w20_2c w20_28 w20_24 w20_18 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_11 g20_10 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20 g19_11 g19_10
  -- 0x168C
  obtain ⟨n22, c22, u22⟩ := s21.block svCsa168c E21.self svCsa168c_end
    ⟨trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem SV n22 0x168E (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock svCsa168c (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
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
  have g22_10 : reg n22 a0 = w38 + BitVec.ofNat 32 4 := by
    rw [rb22, runBlock_reg _ _ _ a0 s21.zero (by decide), g21_10]
  have g22_11 : reg n22 a1 = BitVec.ofNat 32 (ix9 - 4) := by
    rw [rb22, runBlock_reg _ _ _ a1 s21.zero (by decide), g21_11]
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
  have g22_27 : reg n22 (27 : Fin 32) = w38 + BitVec.ofNat 32 4 := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 (ix9 - 4) := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svCsa168c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_10, g21_11, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_18 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m22]; exact w21_18
  have w22_24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m22]; exact w21_24
  have w22_28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m22]; exact w21_28
  have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m22]; exact w21_2c
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m22]; exact w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m22]; exact w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m22]; exact w21_38
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m22]; exact w21_48
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m22]; exact w21_50
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m22]; exact w21_42c
  have b22_14 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m22]; exact b21_14
  have q22_1fc : ∀ j, j < 63 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m22]; exact q21_1fc j hj
  clear q21_1fc b21_14 w21_42c w21_428 w21_424 w21_420 w21_50 w21_48 w21_44 w21_38 w21_34 w21_30 w21_2c w21_28 w21_24 w21_18 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_11 g21_10 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x168E
  obtain ⟨n23, c23, u23⟩ := s22.block svCsa168e E22.self svCsa168e_end
    ⟨trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x1690 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svCsa168e (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans c23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by
    rw [rb23, runBlock_reg _ _ _ sp s22.zero (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (3 : Fin 32) s22.zero (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (4 : Fin 32) s22.zero (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 (ix9 - 4) := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_10 : reg n23 a0 = w38 + BitVec.ofNat 32 4 := by
    rw [rb23, runBlock_reg _ _ _ a0 s22.zero (by decide), g22_10]
  have g23_11 : reg n23 a1 = BitVec.ofNat 32 (ix9 - 4) := by
    rw [rb23, runBlock_reg _ _ _ a1 s22.zero (by decide), g22_11]
  have g23_18 : reg n23 (18 : Fin 32) = out := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by
    rw [rb23, runBlock_reg _ _ _ (20 : Fin 32) s22.zero (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by
    rw [rb23, runBlock_reg _ _ _ (22 : Fin 32) s22.zero (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = w38 + BitVec.ofNat 32 4 := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_24 : reg n23 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svCsa168e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_10, g22_11, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_18 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m23]; exact w22_18
  have w23_24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m23]; exact w22_24
  have w23_28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m23]; exact w22_28
  have w23_2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m23]; exact w22_2c
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m23]; exact w22_38
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m23]; exact w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m23]; exact w22_48
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m23]; exact w22_50
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m23]; exact w22_42c
  have b23_14 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m23]; exact b22_14
  have q23_1fc : ∀ j, j < 63 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m23]; exact q22_1fc j hj
  clear q22_1fc b22_14 w22_42c w22_428 w22_424 w22_420 w22_50 w22_48 w22_44 w22_38 w22_34 w22_30 w22_2c w22_28 w22_24 w22_18 g22_8 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_11 g22_10 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  by_cases hsp : 4 < ix9
  rotate_left
  · -- 0x1690: branch, taken
    obtain ⟨n24, d24, u24⟩ := s23.taken E23.self 0x1878 sv_at_1690
      (by decide) (by rw [g23_11, s23.zero]; exact br_beq_t (by rw [show ix9 - 4 = 0 by omega]; rfl))
    have s24 : St n24.mem SV n24 0x1878 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
    have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 (ix9 - 4) := by rw [u24.regs, g23_8]
    have g24_10 : reg n24 a0 = w38 + BitVec.ofNat 32 4 := by rw [u24.regs, g23_10]
    have g24_11 : reg n24 a1 = BitVec.ofNat 32 (ix9 - 4) := by rw [u24.regs, g23_11]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u24.regs, g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = w38 + BitVec.ofNat 32 4 := by rw [u24.regs, g23_27]
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_18 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m24]; exact w23_18
    have w24_24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m24]; exact w23_24
    have w24_28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m24]; exact w23_28
    have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m24]; exact w23_2c
    have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m24]; exact w23_30
    have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m24]; exact w23_34
    have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m24]; exact w23_38
    have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m24]; exact w23_44
    have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m24]; exact w23_48
    have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m24]; exact w23_50
    have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m24]; exact w23_420
    have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m24]; exact w23_424
    have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m24]; exact w23_428
    have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m24]; exact w23_42c
    have b24_14 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m24]; exact b23_14
    have q24_1fc : ∀ j, j < 63 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m24]; exact q23_1fc j hj
    clear q23_1fc b23_14 w23_42c w23_428 w23_424 w23_420 w23_50 w23_48 w23_44 w23_38 w23_34 w23_30 w23_2c w23_28 w23_24 w23_18 g23_24 g23_27 g23_26 g23_25 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_11 g23_10 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
    -- 0x1878
    obtain ⟨n25, c25, u25⟩ := s24.block svCsa1878 E24.self svCsa1878_end
      ⟨trivial, trivial⟩
    have m25 : n25.mem = n24.mem := u25.mem
    have s25 : St n25.mem SV n25 0x187A (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
    have rb25 : ∀ q, reg n25 q = (runBlock svCsa1878 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
    have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 (ix9 - 4) := by
      rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
    have g25_10 : reg n25 a0 = w38 + BitVec.ofNat 32 4 := by
      rw [rb25, runBlock_reg _ _ _ a0 s24.zero (by decide), g24_10]
    have g25_11 : reg n25 a1 = BitVec.ofNat 32 (ix9 - 4) := by
      rw [rb25, runBlock_reg _ _ _ a1 s24.zero (by decide), g24_11]
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
    have g25_24 : reg n25 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
    have g25_26 : reg n25 (26 : Fin 32) = x26 := by
      rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
    have g25_27 : reg n25 (27 : Fin 32) = w38 + BitVec.ofNat 32 4 := by
      rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
    have g25_25 : reg n25 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb25]; simp +decide only [runBlock, BInstr.run, svCsa1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_10, g24_11, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m25]; exact keep_kk24
    clear keep_kk24
    have w25_18 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m25]; exact w24_18
    have w25_24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m25]; exact w24_24
    have w25_28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m25]; exact w24_28
    have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m25]; exact w24_2c
    have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m25]; exact w24_30
    have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m25]; exact w24_34
    have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m25]; exact w24_38
    have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m25]; exact w24_44
    have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m25]; exact w24_48
    have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m25]; exact w24_50
    have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m25]; exact w24_420
    have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m25]; exact w24_424
    have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m25]; exact w24_428
    have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m25]; exact w24_42c
    have b25_14 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m25]; exact b24_14
    have q25_1fc : ∀ j, j < 63 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m25]; exact q24_1fc j hj
    clear q24_1fc b24_14 w24_42c w24_428 w24_424 w24_420 w24_50 w24_48 w24_44 w24_38 w24_34 w24_30 w24_2c w24_28 w24_24 w24_18 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_11 g24_10 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
    -- 0x187A: j
    obtain ⟨n26, d26, u26⟩ := s25.jump E25.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s25.pc]; decide)
    have s26 : St n26.mem SV n26 0x1882 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans (.single d26)
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 (ix9 - 4) := by rw [u26.regs, g25_8]
    have g26_10 : reg n26 a0 = w38 + BitVec.ofNat 32 4 := by rw [u26.regs, g25_10]
    have g26_11 : reg n26 a1 = BitVec.ofNat 32 (ix9 - 4) := by rw [u26.regs, g25_11]
    have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, g25_19]
    have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [u26.regs, g25_20]
    have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [u26.regs, g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u26.regs, g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u26.regs, g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = w38 + BitVec.ofNat 32 4 := by rw [u26.regs, g25_27]
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m26]; exact keep_kk25
    clear keep_kk25
    have w26_18 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m26]; exact w25_18
    have w26_24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m26]; exact w25_24
    have w26_28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m26]; exact w25_28
    have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m26]; exact w25_2c
    have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m26]; exact w25_30
    have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m26]; exact w25_34
    have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m26]; exact w25_38
    have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m26]; exact w25_44
    have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m26]; exact w25_48
    have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m26]; exact w25_50
    have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m26]; exact w25_420
    have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m26]; exact w25_424
    have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m26]; exact w25_428
    have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m26]; exact w25_42c
    have b26_14 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m26]; exact b25_14
    have q26_1fc : ∀ j, j < 63 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m26]; exact q25_1fc j hj
    clear q25_1fc b25_14 w25_42c w25_428 w25_424 w25_420 w25_50 w25_48 w25_44 w25_38 w25_34 w25_30 w25_2c w25_28 w25_24 w25_18 g25_25 g25_27 g25_26 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_11 g25_10 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
    exact .inl ⟨(fun ⟨ix9', h0', h1', h2', _⟩ => by rw [hr9] at h0'; cases h0'; exact hsp h2'), sv_fail_1882 F E26 s26 t26 (fun x hx => (fR26 x hx).trans (fM x hx).symm) V26 hret g26_2 g26_18 hO g26_3 g26_4⟩
  -- 0x1690: branch, not taken
  obtain ⟨n24, d24, u24⟩ := s23.notTaken E23.self 0x1694 sv_at_1690
    (by decide) (by rw [g23_11, s23.zero]; exact br_beq_f (ofNat_ne_zero (by omega) (by have := w50.isLt; omega)))
  have s24 : St n24.mem SV n24 0x1694 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 (ix9 - 4) := by rw [u24.regs, g23_8]
  have g24_10 : reg n24 a0 = w38 + BitVec.ofNat 32 4 := by rw [u24.regs, g23_10]
  have g24_11 : reg n24 a1 = BitVec.ofNat 32 (ix9 - 4) := by rw [u24.regs, g23_11]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u24.regs, g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = w38 + BitVec.ofNat 32 4 := by rw [u24.regs, g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_18 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m24]; exact w23_18
  have w24_24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m24]; exact w23_24
  have w24_28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m24]; exact w23_28
  have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f) &&& BitVec.ofNat 32 0x1 := by rw [m24]; exact w23_2c
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m24]; exact w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m24]; exact w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m24]; exact w23_38
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m24]; exact w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m24]; exact w23_48
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m24]; exact w23_50
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w38 := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix9 := by rw [m24]; exact w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (w38) + BitVec.ofNat 32 (ix9 + 1) := by rw [m24]; exact w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9 + 1) := by rw [m24]; exact w23_42c
  have b24_14 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m24]; exact b23_14
  have q24_1fc : ∀ j, j < 63 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m24]; exact q23_1fc j hj
  clear q23_1fc b23_14 w23_42c w23_428 w23_424 w23_420 w23_50 w23_48 w23_44 w23_38 w23_34 w23_30 w23_2c w23_28 w23_24 w23_18 g23_24 g23_27 g23_26 g23_25 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_11 g23_10 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  exact .inr ⟨ix9, hr9, hdash, hsp, n24, t24, s24, E24, V24, fR24, g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, w24_18, w24_24, w24_28, w24_2c, w24_30, w24_34, w24_38, w24_44, w24_48, w24_50, w24_420, w24_424, w24_428, w24_42c, b24_14, q24_1fc, keep_kk24.mono (by decide)⟩

end C3.RV32.Sv
