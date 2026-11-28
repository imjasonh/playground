import C3BootProofs.Proofs.SvCs

/-!
# `sigstore::verify`: a signature line's name and signature

From the base64 group loop's end at 0x16D4: the line names the log, and its signature decodes to more than 96 bytes: `sigstore::verify` fails.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCmdl1740 : List BInstr :=
  [.alu .add a0 x0 (27 : Fin 32)]
theorem svCmdl1740_end : blockEnd sigstoreVerifyCode 0x1740 svCmdl1740 = some 0x1742 := by
  simp only [svCmdl1740]
  rw [blockEnd, sv_at_1740]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCmdl1742 : List BInstr :=
  [.alu .add a1 x0 (24 : Fin 32)]
theorem svCmdl1742_end : blockEnd sigstoreVerifyCode 0x1742 svCmdl1742 = some 0x1744 := by
  simp only [svCmdl1742]
  rw [blockEnd, sv_at_1742]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCmdl1754 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a2 x0 0x60, .aluImm .add a1 x0 0x0]
theorem svCmdl1754_end : blockEnd sigstoreVerifyCode 0x1754 svCmdl1754 = some 0x175E := by
  simp only [svCmdl1754]
  rw [blockEnd, sv_at_1754]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1758]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_175c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCmdl1766 : List BInstr :=
  [.aluImm .add a0 sp 0x400, .aluImm .add a3 sp 0x420, .aluImm .add a4 x0 0x60]
theorem svCmdl1766_end : blockEnd sigstoreVerifyCode 0x1766 svCmdl1766 = some 0x1772 := by
  simp only [svCmdl1766]
  rw [blockEnd, sv_at_1766]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_176a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_176e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCmdl1774 : List BInstr :=
  [.alu .add a2 x0 (26 : Fin 32)]
theorem svCmdl1774_end : blockEnd sigstoreVerifyCode 0x1774 svCmdl1774 = some 0x1776 := by
  simp only [svCmdl1774]
  rw [blockEnd, sv_at_1774]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCmdl1878 : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x1A]
theorem svCmdl1878_end : blockEnd sigstoreVerifyCode 0x1878 svCmdl1878 = some 0x187A := by
  simp only [svCmdl1878]
  rw [blockEnd, sv_at_1878]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_cmdl {B out bp x20 x21 x22 x23 x24 x25 x26 x27 f w38 w50 kh w48 w44 kp ckp bl pg gi nl ns1 ni ns10 np w8 wc w10 w2c : Word} {sg bs : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x16D4 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = nl)
    (g0_9 : reg n0 (9 : Fin 32) = ns1)
    (g0_10 : reg n0 a0 = pg)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = gi)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = ni)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = ns10)
    (g0_27 : reg n0 (27 : Fin 32) = np)
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8)
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc)
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (b0_14 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0))
    (q0_1fc : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (hend : pg = w8)
    (hnz : nl ≠ ns1)
    (nm_in : SvIn B np ni.toNat)
    (l_in : SvIn B w48 w44.toNat)
    (hnm : memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat)
    (CK0 : SvCkCode M0)
    (b_in : SvIn B w10 ns10.toNat)
    (hdec : base64Decode (memBytes M0 w10 ns10.toNat) = some bs)
    (hbig : 0x60 < bs.length) :
    (¬ ((False) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((False) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1642 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem []) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x16D4: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_16d4 (off' := 0x16D6) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0x8 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0x16D6 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = nl := by rw [u1.regs, upd_ne (by decide) (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = ns1 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_9]
  have g1_10 : reg n1 a0 = pg := by rw [u1.regs, upd_ne (by decide) (by decide), g0_10]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, upd_ne (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = gi := by rw [u1.regs, upd_ne (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = ni := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = ns10 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = np := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_11 : reg n1 a1 = w8 := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0x8 by sv_addr, w0_8]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m1]; exact w0_8
  have w1_c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m1]; exact w0_c
  have w1_10 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m1]; exact w0_10
  have w1_18 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m1]; exact w0_18
  have w1_24 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m1]; exact w0_24
  have w1_28 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m1]; exact w0_28
  have w1_2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m1]; exact w0_2c
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m1]; exact w0_30
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m1]; exact w0_34
  have w1_38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m1]; exact w0_38
  have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m1]; exact w0_44
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m1]; exact w0_48
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  have b1_14 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m1]; exact b0_14
  have q1_1fc : ∀ j, j < 63 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m1]; exact q0_1fc j hj
  -- 0x16D6: branch, taken
  obtain ⟨n2, d2, u2⟩ := s1.taken E1.self 0x173C sv_at_16d6
    (by decide) (by rw [g1_10, g1_11]; exact br_beq_t hend)
  have s2 : St n2.mem SV n2 0x173C (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = nl := by rw [u2.regs, g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = ns1 := by rw [u2.regs, g1_9]
  have g2_10 : reg n2 a0 = pg := by rw [u2.regs, g1_10]
  have g2_11 : reg n2 a1 = w8 := by rw [u2.regs, g1_11]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [u2.regs, g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = gi := by rw [u2.regs, g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [u2.regs, g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [u2.regs, g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = ni := by rw [u2.regs, g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [u2.regs, g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = ns10 := by rw [u2.regs, g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = np := by rw [u2.regs, g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m2]; exact w1_8
  have w2_c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m2]; exact w1_c
  have w2_10 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m2]; exact w1_10
  have w2_18 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m2]; exact w1_18
  have w2_24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m2]; exact w1_24
  have w2_28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m2]; exact w1_28
  have w2_2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m2]; exact w1_2c
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m2]; exact w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m2]; exact w1_34
  have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m2]; exact w1_38
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m2]; exact w1_44
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m2]; exact w1_48
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
  have b2_14 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m2]; exact b1_14
  have q2_1fc : ∀ j, j < 63 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m2]; exact q1_1fc j hj
  clear q1_1fc b1_14 w1_50 w1_48 w1_44 w1_38 w1_34 w1_30 w1_2c w1_28 w1_24 w1_18 w1_10 w1_c w1_8 g1_11 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_10 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x173C: branch, not taken
  obtain ⟨n3, d3, u3⟩ := s2.notTaken E2.self 0x1740 sv_at_173c
    (by decide) (by rw [g2_8, g2_9]; exact br_beq_f hnz)
  have s3 : St n3.mem SV n3 0x1740 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = nl := by rw [u3.regs, g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = ns1 := by rw [u3.regs, g2_9]
  have g3_10 : reg n3 a0 = pg := by rw [u3.regs, g2_10]
  have g3_11 : reg n3 a1 = w8 := by rw [u3.regs, g2_11]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = gi := by rw [u3.regs, g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = ni := by rw [u3.regs, g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = ns10 := by rw [u3.regs, g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = np := by rw [u3.regs, g2_27]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m3]; exact w2_8
  have w3_c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m3]; exact w2_c
  have w3_10 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m3]; exact w2_10
  have w3_18 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m3]; exact w2_18
  have w3_24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m3]; exact w2_24
  have w3_28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m3]; exact w2_28
  have w3_2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m3]; exact w2_2c
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m3]; exact w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m3]; exact w2_34
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m3]; exact w2_38
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m3]; exact w2_44
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m3]; exact w2_48
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  have b3_14 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m3]; exact b2_14
  have q3_1fc : ∀ j, j < 63 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m3]; exact q2_1fc j hj
  clear q2_1fc b2_14 w2_50 w2_48 w2_44 w2_38 w2_34 w2_30 w2_2c w2_28 w2_24 w2_18 w2_10 w2_c w2_8 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_11 g2_10 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x1740
  obtain ⟨n4, c4, u4⟩ := s3.block svCmdl1740 E3.self svCmdl1740_end
    ⟨trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x1742 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svCmdl1740 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_8 : reg n4 (8 : Fin 32) = nl := by
    rw [rb4, runBlock_reg _ _ _ (8 : Fin 32) s3.zero (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = ns1 := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
  have g4_11 : reg n4 a1 = w8 := by
    rw [rb4, runBlock_reg _ _ _ a1 s3.zero (by decide), g3_11]
  have g4_18 : reg n4 (18 : Fin 32) = out := by
    rw [rb4, runBlock_reg _ _ _ (18 : Fin 32) s3.zero (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by
    rw [rb4, runBlock_reg _ _ _ (20 : Fin 32) s3.zero (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = gi := by
    rw [rb4, runBlock_reg _ _ _ (21 : Fin 32) s3.zero (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by
    rw [rb4, runBlock_reg _ _ _ (22 : Fin 32) s3.zero (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by
    rw [rb4, runBlock_reg _ _ _ (23 : Fin 32) s3.zero (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = ni := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = ns10 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = np := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_10 : reg n4 a0 = np := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svCmdl1740, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_11, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m4]; exact w3_8
  have w4_c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m4]; exact w3_c
  have w4_10 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m4]; exact w3_10
  have w4_18 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m4]; exact w3_18
  have w4_24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m4]; exact w3_24
  have w4_28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m4]; exact w3_28
  have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m4]; exact w3_2c
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m4]; exact w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m4]; exact w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m4]; exact w3_38
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m4]; exact w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m4]; exact w3_48
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m4]; exact w3_50
  have b4_14 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m4]; exact b3_14
  have q4_1fc : ∀ j, j < 63 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m4]; exact q3_1fc j hj
  clear q3_1fc b3_14 w3_50 w3_48 w3_44 w3_38 w3_34 w3_30 w3_2c w3_28 w3_24 w3_18 w3_10 w3_c w3_8 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_11 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x1742
  obtain ⟨n5, c5, u5⟩ := s4.block svCmdl1742 E4.self svCmdl1742_end
    ⟨trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x1744 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svCmdl1742 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_8 : reg n5 (8 : Fin 32) = nl := by
    rw [rb5, runBlock_reg _ _ _ (8 : Fin 32) s4.zero (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = ns1 := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_10 : reg n5 a0 = np := by
    rw [rb5, runBlock_reg _ _ _ a0 s4.zero (by decide), g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = gi := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = ni := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = ns10 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = np := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_11 : reg n5 a1 = ni := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svCmdl1742, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_10, g4_11, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m5]; exact w4_8
  have w5_c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m5]; exact w4_c
  have w5_10 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m5]; exact w4_10
  have w5_18 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m5]; exact w4_18
  have w5_24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m5]; exact w4_24
  have w5_28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m5]; exact w4_28
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m5]; exact w4_2c
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m5]; exact w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m5]; exact w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m5]; exact w4_38
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m5]; exact w4_48
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have b5_14 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m5]; exact b4_14
  have q5_1fc : ∀ j, j < 63 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_1fc j hj
  clear q4_1fc b4_14 w4_50 w4_48 w4_44 w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 w4_18 w4_10 w4_c w4_8 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_11 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x1744: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_1744 (off' := 0x1746) (by decide)
    (by rw [g5_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0x1746 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = nl := by rw [u6.regs, upd_ne (by decide) (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = ns1 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
  have g6_10 : reg n6 a0 = np := by rw [u6.regs, upd_ne (by decide) (by decide), g5_10]
  have g6_11 : reg n6 a1 = ni := by rw [u6.regs, upd_ne (by decide) (by decide), g5_11]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = gi := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = ni := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = ns10 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = np := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_12 : reg n6 a2 = w48 := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w5_48]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m6]; exact w5_8
  have w6_c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m6]; exact w5_c
  have w6_10 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m6]; exact w5_10
  have w6_18 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m6]; exact w5_18
  have w6_24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m6]; exact w5_24
  have w6_28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m6]; exact w5_28
  have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m6]; exact w5_2c
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m6]; exact w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m6]; exact w5_34
  have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m6]; exact w5_38
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m6]; exact w5_48
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
  have b6_14 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m6]; exact b5_14
  have q6_1fc : ∀ j, j < 63 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_1fc j hj
  clear q5_1fc b5_14 w5_50 w5_48 w5_44 w5_38 w5_34 w5_30 w5_2c w5_28 w5_24 w5_18 w5_10 w5_c w5_8 g5_11 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x1746: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_1746 (off' := 0x1748) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0x1748 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = nl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = ns1 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_9]
  have g7_10 : reg n7 a0 = np := by rw [u7.regs, upd_ne (by decide) (by decide), g6_10]
  have g7_11 : reg n7 a1 = ni := by rw [u7.regs, upd_ne (by decide) (by decide), g6_11]
  have g7_12 : reg n7 a2 = w48 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_12]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = gi := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = ni := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = ns10 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = np := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
  have g7_13 : reg n7 a3 = w44 := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w6_44]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m7]; exact w6_8
  have w7_c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m7]; exact w6_c
  have w7_10 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m7]; exact w6_10
  have w7_18 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m7]; exact w6_18
  have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m7]; exact w6_24
  have w7_28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m7]; exact w6_28
  have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m7]; exact w6_2c
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m7]; exact w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m7]; exact w6_34
  have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m7]; exact w6_38
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m7]; exact w6_44
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m7]; exact w6_48
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
  have b7_14 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m7]; exact b6_14
  have q7_1fc : ∀ j, j < 63 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m7]; exact q6_1fc j hj
  clear q6_1fc b6_14 w6_50 w6_48 w6_44 w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 w6_18 w6_10 w6_c w6_8 g6_12 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x1748: sv_sneF
  obtain ⟨n8, c8, s8, rk8, a0_8, K8, fr8⟩ := sv_sneF (pl := ni.toNat) (ql := w44.toNat)
    F E7 s7 sv_at_1748 sv_at_174c (by decide) (by decide) g7_2
    g7_10 (by rw [g7_11, ofNat_toNat_self]) g7_12 (by rw [g7_13, ofNat_toNat_self]) (.inl nm_in) (.inl l_in)
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keepL K8 (by decide)
  rw [sv_mbRo FW fR7 (.inl nm_in), sv_mbRo FW fR7 (.inl l_in)] at a0_8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rk8 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk8 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk8 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = nl := by rw [rk8 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = ns1 := by rw [rk8 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rk8 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rk8 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [rk8 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = gi := by rw [rk8 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [rk8 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [rk8 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = ni := by rw [rk8 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [rk8 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = ns10 := by rw [rk8 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = np := by rw [rk8 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [] := keep_kk7.trans K8
  clear keep_kk7
  have w8_8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K8.w32 (by decide) (by decide)).trans w7_8
  have w8_c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K8.w32 (by decide) (by decide)).trans w7_c
  have w8_10 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K8.w32 (by decide) (by decide)).trans w7_10
  have w8_18 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K8.w32 (by decide) (by decide)).trans w7_18
  have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K8.w32 (by decide) (by decide)).trans w7_24
  have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K8.w32 (by decide) (by decide)).trans w7_28
  have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K8.w32 (by decide) (by decide)).trans w7_2c
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K8.w32 (by decide) (by decide)).trans w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K8.w32 (by decide) (by decide)).trans w7_34
  have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K8.w32 (by decide) (by decide)).trans w7_38
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K8.w32 (by decide) (by decide)).trans w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K8.w32 (by decide) (by decide)).trans w7_48
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K8.w32 (by decide) (by decide)).trans w7_50
  have b8_14 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K8.b8 (by decide) (by decide)).trans b7_14
  have q8_1fc : ∀ j, j < 63 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_1fc j hj)
  clear q7_1fc b7_14 w7_50 w7_48 w7_44 w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 w7_18 w7_10 w7_c w7_8 g7_13 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_12 g7_11 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  by_cases hf : False
  rotate_left
  · have g8_10 : reg n8 a0 = BitVec.ofNat 32 0 := by rw [a0_8, ite_eq_left hnm]; rfl
    -- 0x1750: branch, not taken
    obtain ⟨n9, d9, u9⟩ := s8.notTaken E8.self 0x1754 sv_at_1750
      (by decide) (by rw [g8_10, s8.zero]; decide)
    have s9 : St n9.mem SV n9 0x1754 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = nl := by rw [u9.regs, g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = ns1 := by rw [u9.regs, g8_9]
    have g9_10 : reg n9 a0 = BitVec.ofNat 32 0x0 := by rw [u9.regs, g8_10]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = gi := by rw [u9.regs, g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = ni := by rw [u9.regs, g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = ns10 := by rw [u9.regs, g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = np := by rw [u9.regs, g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m9]; exact w8_8
    have w9_c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m9]; exact w8_c
    have w9_10 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m9]; exact w8_10
    have w9_18 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m9]; exact w8_18
    have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m9]; exact w8_24
    have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m9]; exact w8_28
    have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m9]; exact w8_2c
    have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m9]; exact w8_30
    have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m9]; exact w8_34
    have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m9]; exact w8_38
    have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m9]; exact w8_44
    have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m9]; exact w8_48
    have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
    have b9_14 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m9]; exact b8_14
    have q9_1fc : ∀ j, j < 63 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m9]; exact q8_1fc j hj
    clear q8_1fc b8_14 w8_50 w8_48 w8_44 w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 w8_18 w8_10 w8_c w8_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 K8 a0_8 rk8 s8 c8
    -- 0x1754
    obtain ⟨n10, c10, u10⟩ := s9.block svCmdl1754 E9.self svCmdl1754_end
      ⟨trivial, trivial, trivial, trivial⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have s10 : St n10.mem SV n10 0x175E (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have rb10 : ∀ q, reg n10 q = (runBlock svCmdl1754 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
    have g10_8 : reg n10 (8 : Fin 32) = nl := by
      rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = ns1 := by
      rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
    have g10_18 : reg n10 (18 : Fin 32) = out := by
      rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by
      rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = x20 := by
      rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = gi := by
      rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = x22 := by
      rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = x23 := by
      rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = ni := by
      rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = x25 := by
      rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = ns10 := by
      rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = np := by
      rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
    have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
      rw [rb10]; simp +decide only [runBlock, BInstr.run, svCmdl1754, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g10_11 : reg n10 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb10]; simp +decide only [runBlock, BInstr.run, svCmdl1754, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g10_12 : reg n10 a2 = BitVec.ofNat 32 0x60 := by
      rw [rb10]; simp +decide only [runBlock, BInstr.run, svCmdl1754, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk10 : SvKeepL B n0.mem n10.mem [] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m10]; exact w9_8
    have w10_c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m10]; exact w9_c
    have w10_10 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m10]; exact w9_10
    have w10_18 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m10]; exact w9_18
    have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m10]; exact w9_24
    have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m10]; exact w9_28
    have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m10]; exact w9_2c
    have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m10]; exact w9_30
    have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m10]; exact w9_34
    have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m10]; exact w9_38
    have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
    have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m10]; exact w9_48
    have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
    have b10_14 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m10]; exact b9_14
    have q10_1fc : ∀ j, j < 63 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_1fc j hj
    clear q9_1fc b9_14 w9_50 w9_48 w9_44 w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 w9_18 w9_10 w9_c w9_8 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9 g8_10
    -- 0x175E: sv_ms2F
    obtain ⟨n11, c11, s11, rk11, K11, fr11⟩ := sv_ms2F (c := 0x420) (N := 0x60)
      F E10 s10 sv_at_175e sv_at_1762 (by decide) (by decide)
      g10_10 g10_11 g10_12 (by decide)
    have t11 : Steps n0 n11 := t10.trans c11
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.keepL K11 (by decide)
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rk11 sp (by decide), g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk11 (3 : Fin 32) (by decide), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk11 (4 : Fin 32) (by decide), g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = nl := by rw [rk11 (8 : Fin 32) (by decide), g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = ns1 := by rw [rk11 (9 : Fin 32) (by decide), g10_9]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rk11 (18 : Fin 32) (by decide), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rk11 (19 : Fin 32) (by decide), g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [rk11 (20 : Fin 32) (by decide), g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = gi := by rw [rk11 (21 : Fin 32) (by decide), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [rk11 (22 : Fin 32) (by decide), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [rk11 (23 : Fin 32) (by decide), g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = ni := by rw [rk11 (24 : Fin 32) (by decide), g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [rk11 (25 : Fin 32) (by decide), g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = ns10 := by rw [rk11 (26 : Fin 32) (by decide), g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = np := by rw [rk11 (27 : Fin 32) (by decide), g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x60)] := keep_kk10.trans K11
    clear keep_kk10
    have w11_8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K11.w32 (by decide) (by decide)).trans w10_8
    have w11_c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K11.w32 (by decide) (by decide)).trans w10_c
    have w11_10 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K11.w32 (by decide) (by decide)).trans w10_10
    have w11_18 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K11.w32 (by decide) (by decide)).trans w10_18
    have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K11.w32 (by decide) (by decide)).trans w10_24
    have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K11.w32 (by decide) (by decide)).trans w10_28
    have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K11.w32 (by decide) (by decide)).trans w10_2c
    have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K11.w32 (by decide) (by decide)).trans w10_30
    have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K11.w32 (by decide) (by decide)).trans w10_34
    have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K11.w32 (by decide) (by decide)).trans w10_38
    have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K11.w32 (by decide) (by decide)).trans w10_44
    have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K11.w32 (by decide) (by decide)).trans w10_48
    have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K11.w32 (by decide) (by decide)).trans w10_50
    have b11_14 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K11.b8 (by decide) (by decide)).trans b10_14
    have q11_1fc : ∀ j, j < 63 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_1fc j hj)
    clear q10_1fc b10_14 w10_50 w10_48 w10_44 w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 w10_18 w10_10 w10_c w10_8 g10_12 g10_11 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
    -- 0x1766
    obtain ⟨n12, c12, u12⟩ := s11.block svCmdl1766 E11.self svCmdl1766_end
      ⟨trivial, trivial, trivial, trivial⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have s12 : St n12.mem SV n12 0x1772 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have rb12 : ∀ q, reg n12 q = (runBlock svCmdl1766 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
    have g12_9 : reg n12 (9 : Fin 32) = ns1 := by
      rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
    have g12_18 : reg n12 (18 : Fin 32) = out := by
      rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by
      rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = x20 := by
      rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = gi := by
      rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by
      rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by
      rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = ni := by
      rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = x25 := by
      rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = ns10 := by
      rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = np := by
      rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
    have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
      rw [rb12]; simp +decide only [runBlock, BInstr.run, svCmdl1766, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g12_13 : reg n12 a3 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
      rw [rb12]; simp +decide only [runBlock, BInstr.run, svCmdl1766, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g12_14 : reg n12 a4 = BitVec.ofNat 32 0x60 := by
      rw [rb12]; simp +decide only [runBlock, BInstr.run, svCmdl1766, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x60)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m12]; exact w11_8
    have w12_c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m12]; exact w11_c
    have w12_10 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m12]; exact w11_10
    have w12_18 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m12]; exact w11_18
    have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m12]; exact w11_24
    have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m12]; exact w11_28
    have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m12]; exact w11_2c
    have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m12]; exact w11_30
    have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m12]; exact w11_34
    have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m12]; exact w11_38
    have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m12]; exact w11_44
    have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m12]; exact w11_48
    have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
    have b12_14 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m12]; exact b11_14
    have q12_1fc : ∀ j, j < 63 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m12]; exact q11_1fc j hj
    clear q11_1fc b11_14 w11_50 w11_48 w11_44 w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 w11_18 w11_10 w11_c w11_8 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 K11 rk11 s11 c11
    -- 0x1772: lw
    obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_1772 (off' := 0x1774) (by decide)
      (by rw [g12_2, show B + 0x21A0 + 0x10 = B + 0x21A0 + BitVec.ofNat 32 0x10 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s13 : St n13.mem SV n13 0x1774 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
    have t13 : Steps n0 n13 := t12.trans (.single d13)
    have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
    have E13 : SvCode n13.mem := E12.fr F fr13
    have V13 : SvSaves B n13.mem v := V12.same m13
    have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
    have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
    have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
    have g13_8 : reg n13 (8 : Fin 32) = nl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_8]
    have g13_9 : reg n13 (9 : Fin 32) = ns1 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_9]
    have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_10]
    have g13_13 : reg n13 a3 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_13]
    have g13_14 : reg n13 a4 = BitVec.ofNat 32 0x60 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_14]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = gi := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = ni := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = ns10 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = np := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
    have g13_11 : reg n13 a1 = w10 := by
      rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g12_2, show B + 0x21A0 + 0x10 = B + 0x21A0 + BitVec.ofNat 32 0x10 by sv_addr, w12_10]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x60)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m13]; exact w12_8
    have w13_c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m13]; exact w12_c
    have w13_10 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m13]; exact w12_10
    have w13_18 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m13]; exact w12_18
    have w13_24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m13]; exact w12_24
    have w13_28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m13]; exact w12_28
    have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m13]; exact w12_2c
    have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m13]; exact w12_30
    have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m13]; exact w12_34
    have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m13]; exact w12_38
    have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m13]; exact w12_44
    have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m13]; exact w12_48
    have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
    have b13_14 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m13]; exact b12_14
    have q13_1fc : ∀ j, j < 63 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m13]; exact q12_1fc j hj
    clear q12_1fc b12_14 w12_50 w12_48 w12_44 w12_38 w12_34 w12_30 w12_2c w12_28 w12_24 w12_18 w12_10 w12_c w12_8 g12_14 g12_13 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
    -- 0x1774
    obtain ⟨n14, c14, u14⟩ := s13.block svCmdl1774 E13.self svCmdl1774_end
      ⟨trivial, trivial⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have s14 : St n14.mem SV n14 0x1776 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have rb14 : ∀ q, reg n14 q = (runBlock svCmdl1774 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
    have g14_8 : reg n14 (8 : Fin 32) = nl := by
      rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
    have g14_9 : reg n14 (9 : Fin 32) = ns1 := by
      rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
    have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
      rw [rb14, runBlock_reg _ _ _ a0 s13.zero (by decide), g13_10]
    have g14_11 : reg n14 a1 = w10 := by
      rw [rb14, runBlock_reg _ _ _ a1 s13.zero (by decide), g13_11]
    have g14_13 : reg n14 a3 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
      rw [rb14, runBlock_reg _ _ _ a3 s13.zero (by decide), g13_13]
    have g14_14 : reg n14 a4 = BitVec.ofNat 32 0x60 := by
      rw [rb14, runBlock_reg _ _ _ a4 s13.zero (by decide), g13_14]
    have g14_18 : reg n14 (18 : Fin 32) = out := by
      rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by
      rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
    have g14_20 : reg n14 (20 : Fin 32) = x20 := by
      rw [rb14, runBlock_reg _ _ _ (20 : Fin 32) s13.zero (by decide), g13_20]
    have g14_21 : reg n14 (21 : Fin 32) = gi := by
      rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
    have g14_22 : reg n14 (22 : Fin 32) = x22 := by
      rw [rb14, runBlock_reg _ _ _ (22 : Fin 32) s13.zero (by decide), g13_22]
    have g14_23 : reg n14 (23 : Fin 32) = x23 := by
      rw [rb14, runBlock_reg _ _ _ (23 : Fin 32) s13.zero (by decide), g13_23]
    have g14_24 : reg n14 (24 : Fin 32) = ni := by
      rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = x25 := by
      rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = ns10 := by
      rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = np := by
      rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
    have g14_12 : reg n14 a2 = ns10 := by
      rw [rb14]; simp +decide only [runBlock, BInstr.run, svCmdl1774, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_11, g13_13, g13_14, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x60)] := by rw [m14]; exact keep_kk13
    clear keep_kk13
    have w14_8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m14]; exact w13_8
    have w14_c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m14]; exact w13_c
    have w14_10 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m14]; exact w13_10
    have w14_18 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m14]; exact w13_18
    have w14_24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m14]; exact w13_24
    have w14_28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m14]; exact w13_28
    have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m14]; exact w13_2c
    have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m14]; exact w13_30
    have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m14]; exact w13_34
    have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m14]; exact w13_38
    have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m14]; exact w13_44
    have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m14]; exact w13_48
    have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m14]; exact w13_50
    have b14_14 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m14]; exact b13_14
    have q14_1fc : ∀ j, j < 63 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m14]; exact q13_1fc j hj
    clear q13_1fc b13_14 w13_50 w13_48 w13_44 w13_38 w13_34 w13_30 w13_2c w13_28 w13_24 w13_18 w13_10 w13_c w13_8 g13_11 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_14 g13_13 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
    -- 0x1776: sv_b64F
    obtain ⟨n15, c15, s15, sp15, rk15, K15, Ok15, Bad15, fr15⟩ := sv_b64F (rc := 0x400) (oc := 0x420) (nl := (ns10).toNat) (L := 0x60)
      F E14 (CK0.sv FW fR14) s14 sv_at_1776 sv_at_177a (by decide) (by decide) g14_2
      g14_10 g14_11 (by rw [g14_12, ofNat_toNat_self]) g14_13 g14_14
      (by decide) (by decide) (by decide) (by decide) (.inl b_in)
    have t15 : Steps n0 n15 := t14.trans c15
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.keepL K15 (by decide)
    rw [sv_mbRo FW fR14 (.inl b_in)] at Ok15 Bad15
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk15 (3 : Fin 32) (by decide), g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk15 (4 : Fin 32) (by decide), g14_4]
    have g15_8 : reg n15 (8 : Fin 32) = nl := by rw [rk15 (8 : Fin 32) (by decide), g14_8]
    have g15_9 : reg n15 (9 : Fin 32) = ns1 := by rw [rk15 (9 : Fin 32) (by decide), g14_9]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rk15 (18 : Fin 32) (by decide), g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rk15 (19 : Fin 32) (by decide), g14_19]
    have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [rk15 (20 : Fin 32) (by decide), g14_20]
    have g15_21 : reg n15 (21 : Fin 32) = gi := by rw [rk15 (21 : Fin 32) (by decide), g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [rk15 (22 : Fin 32) (by decide), g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [rk15 (23 : Fin 32) (by decide), g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = ni := by rw [rk15 (24 : Fin 32) (by decide), g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [rk15 (25 : Fin 32) (by decide), g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = ns10 := by rw [rk15 (26 : Fin 32) (by decide), g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = np := by rw [rk15 (27 : Fin 32) (by decide), g14_27]
    have g15_2 : reg n15 sp = B + 0x21A0 := sp15
    have z15 := Bad15 fun b h => by rw [hdec] at h; cases h; exact hbig
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := keep_kk14.trans K15
    clear keep_kk14
    have w15_8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K15.w32 (by decide) (by decide)).trans w14_8
    have w15_c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K15.w32 (by decide) (by decide)).trans w14_c
    have w15_10 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K15.w32 (by decide) (by decide)).trans w14_10
    have w15_18 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K15.w32 (by decide) (by decide)).trans w14_18
    have w15_24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K15.w32 (by decide) (by decide)).trans w14_24
    have w15_28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K15.w32 (by decide) (by decide)).trans w14_28
    have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K15.w32 (by decide) (by decide)).trans w14_2c
    have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K15.w32 (by decide) (by decide)).trans w14_30
    have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K15.w32 (by decide) (by decide)).trans w14_34
    have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K15.w32 (by decide) (by decide)).trans w14_38
    have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K15.w32 (by decide) (by decide)).trans w14_44
    have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K15.w32 (by decide) (by decide)).trans w14_48
    have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K15.w32 (by decide) (by decide)).trans w14_50
    have b15_14 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K15.b8 (by decide) (by decide)).trans b14_14
    have q15_1fc : ∀ j, j < 63 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_1fc j hj)
    have b15_400 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := z15
    clear q14_1fc b14_14 w14_50 w14_48 w14_44 w14_38 w14_34 w14_30 w14_2c w14_28 w14_24 w14_18 w14_10 w14_c w14_8 g14_12 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_14 g14_13 g14_11 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
    -- 0x177E: lbu
    obtain ⟨n16, d16, u16⟩ := s15.lbu E15.self sv_at_177e (off' := 0x1782) (by decide)
    have s16 : St n16.mem SV n16 0x1782 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
    have g16_8 : reg n16 (8 : Fin 32) = nl := by rw [u16.regs, upd_ne (by decide) (by decide), g15_8]
    have g16_9 : reg n16 (9 : Fin 32) = ns1 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = gi := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = ni := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = ns10 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = np := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
    have g16_10 : reg n16 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g15_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr, b15_400]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m16]; exact w15_8
    have w16_c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m16]; exact w15_c
    have w16_10 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m16]; exact w15_10
    have w16_18 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m16]; exact w15_18
    have w16_24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m16]; exact w15_24
    have w16_28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m16]; exact w15_28
    have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m16]; exact w15_2c
    have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m16]; exact w15_30
    have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m16]; exact w15_34
    have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m16]; exact w15_38
    have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m16]; exact w15_44
    have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m16]; exact w15_48
    have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
    have b16_14 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m16]; exact b15_14
    have b16_400 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m16]; exact b15_400
    have q16_1fc : ∀ j, j < 63 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m16]; exact q15_1fc j hj
    clear b15_400 q15_1fc b15_14 w15_50 w15_48 w15_44 w15_38 w15_34 w15_30 w15_2c w15_28 w15_24 w15_18 w15_10 w15_c w15_8 z15 g15_2 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 V15 E15 fR15 t15 fr15 Bad15 Ok15 K15 rk15 sp15 s15 c15
    -- 0x1782: branch, taken
    obtain ⟨n17, d17, u17⟩ := s16.taken E16.self 0x1878 sv_at_1782
      (by decide) (by rw [g16_10, s16.zero]; decide)
    have s17 : St n17.mem SV n17 0x1878 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = nl := by rw [u17.regs, g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = ns1 := by rw [u17.regs, g16_9]
    have g17_10 : reg n17 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u17.regs, g16_10]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = gi := by rw [u17.regs, g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = ni := by rw [u17.regs, g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = ns10 := by rw [u17.regs, g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = np := by rw [u17.regs, g16_27]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m17]; exact w16_8
    have w17_c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m17]; exact w16_c
    have w17_10 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m17]; exact w16_10
    have w17_18 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m17]; exact w16_18
    have w17_24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m17]; exact w16_24
    have w17_28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m17]; exact w16_28
    have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m17]; exact w16_2c
    have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m17]; exact w16_30
    have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m17]; exact w16_34
    have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m17]; exact w16_38
    have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m17]; exact w16_44
    have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m17]; exact w16_48
    have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
    have b17_14 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m17]; exact b16_14
    have b17_400 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m17]; exact b16_400
    have q17_1fc : ∀ j, j < 63 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m17]; exact q16_1fc j hj
    clear q16_1fc b16_400 b16_14 w16_50 w16_48 w16_44 w16_38 w16_34 w16_30 w16_2c w16_28 w16_24 w16_18 w16_10 w16_c w16_8 g16_10 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    -- 0x1878
    obtain ⟨n18, c18, u18⟩ := s17.block svCmdl1878 E17.self svCmdl1878_end
      ⟨trivial, trivial⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have s18 : St n18.mem SV n18 0x187A (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have rb18 : ∀ q, reg n18 q = (runBlock svCmdl1878 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
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
    have g18_8 : reg n18 (8 : Fin 32) = nl := by
      rw [rb18, runBlock_reg _ _ _ (8 : Fin 32) s17.zero (by decide), g17_8]
    have g18_9 : reg n18 (9 : Fin 32) = ns1 := by
      rw [rb18, runBlock_reg _ _ _ (9 : Fin 32) s17.zero (by decide), g17_9]
    have g18_10 : reg n18 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [rb18, runBlock_reg _ _ _ a0 s17.zero (by decide), g17_10]
    have g18_18 : reg n18 (18 : Fin 32) = out := by
      rw [rb18, runBlock_reg _ _ _ (18 : Fin 32) s17.zero (by decide), g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by
      rw [rb18, runBlock_reg _ _ _ (19 : Fin 32) s17.zero (by decide), g17_19]
    have g18_20 : reg n18 (20 : Fin 32) = x20 := by
      rw [rb18, runBlock_reg _ _ _ (20 : Fin 32) s17.zero (by decide), g17_20]
    have g18_21 : reg n18 (21 : Fin 32) = gi := by
      rw [rb18, runBlock_reg _ _ _ (21 : Fin 32) s17.zero (by decide), g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = x22 := by
      rw [rb18, runBlock_reg _ _ _ (22 : Fin 32) s17.zero (by decide), g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = x23 := by
      rw [rb18, runBlock_reg _ _ _ (23 : Fin 32) s17.zero (by decide), g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = ni := by
      rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
    have g18_26 : reg n18 (26 : Fin 32) = ns10 := by
      rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = np := by
      rw [rb18, runBlock_reg _ _ _ (27 : Fin 32) s17.zero (by decide), g17_27]
    have g18_25 : reg n18 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb18]; simp +decide only [runBlock, BInstr.run, svCmdl1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_10, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m18]; exact keep_kk17
    clear keep_kk17
    have w18_8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m18]; exact w17_8
    have w18_c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m18]; exact w17_c
    have w18_10 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m18]; exact w17_10
    have w18_18 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m18]; exact w17_18
    have w18_24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m18]; exact w17_24
    have w18_28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m18]; exact w17_28
    have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m18]; exact w17_2c
    have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m18]; exact w17_30
    have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m18]; exact w17_34
    have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m18]; exact w17_38
    have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m18]; exact w17_44
    have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m18]; exact w17_48
    have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
    have b18_14 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m18]; exact b17_14
    have b18_400 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m18]; exact b17_400
    have q18_1fc : ∀ j, j < 63 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m18]; exact q17_1fc j hj
    clear q17_1fc b17_400 b17_14 w17_50 w17_48 w17_44 w17_38 w17_34 w17_30 w17_2c w17_28 w17_24 w17_18 w17_10 w17_c w17_8 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
    -- 0x187A: j
    obtain ⟨n19, d19, u19⟩ := s18.jump E18.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s18.pc]; decide)
    have s19 : St n19.mem SV n19 0x1882 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
    have g19_8 : reg n19 (8 : Fin 32) = nl := by rw [u19.regs, g18_8]
    have g19_9 : reg n19 (9 : Fin 32) = ns1 := by rw [u19.regs, g18_9]
    have g19_10 : reg n19 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u19.regs, g18_10]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = gi := by rw [u19.regs, g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = ni := by rw [u19.regs, g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u19.regs, g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = ns10 := by rw [u19.regs, g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = np := by rw [u19.regs, g18_27]
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m19]; exact w18_8
    have w19_c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m19]; exact w18_c
    have w19_10 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m19]; exact w18_10
    have w19_18 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m19]; exact w18_18
    have w19_24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m19]; exact w18_24
    have w19_28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m19]; exact w18_28
    have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m19]; exact w18_2c
    have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m19]; exact w18_30
    have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m19]; exact w18_34
    have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m19]; exact w18_38
    have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m19]; exact w18_44
    have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m19]; exact w18_48
    have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m19]; exact w18_50
    have b19_14 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m19]; exact b18_14
    have b19_400 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m19]; exact b18_400
    have q19_1fc : ∀ j, j < 63 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m19]; exact q18_1fc j hj
    clear q18_1fc b18_400 b18_14 w18_50 w18_48 w18_44 w18_38 w18_34 w18_30 w18_2c w18_28 w18_24 w18_18 w18_10 w18_c w18_8 g18_25 g18_27 g18_26 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hf h0'), sv_fail_1882 F E19 s19 t19 (fun x hx => (fR19 x hx).trans (fM x hx).symm) V19 hret g19_2 g19_18 hO g19_3 g19_4 (by rw [g19_25]; sv_code)⟩
  exact hf.elim


end C3.RV32.Sv
