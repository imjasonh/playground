import C3BootProofs.Proofs.SvGt
import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: the parsed timestamp

From 0x12BE to the TSA loop at 0x1344: `sigstore::verify` copies the timestamp's fields, with the signature's `r` and `s`, into its `Timestamp` at offset 0x170 of the frame, and points the loop at the trust root's TSA keys.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTsv12be : List BInstr :=
  [.aluImm .add a0 sp 0x1FC, .aluImm .add a1 sp 0x380, .aluImm .add a2 x0 0x5F]
theorem svTsv12be_end : blockEnd sigstoreVerifyCode 0x12BE svTsv12be = some 0x12C6 := by
  simp only [svTsv12be]
  rw [blockEnd, sv_at_12be]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_12c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_12c2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsv12d4 : List BInstr :=
  [.aluImm .srl a0 (8 : Fin 32) 0x8, .aluImm .srl a1 a0 0x8, .aluImm .srl a2 a0 0x10]
theorem svTsv12d4_end : blockEnd sigstoreVerifyCode 0x12D4 svTsv12d4 = some 0x12E0 := by
  simp only [svTsv12d4]
  rw [blockEnd, sv_at_12d4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_12d8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_12dc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsv12f2 : List BInstr :=
  [.aluImm .add (26 : Fin 32) sp 0x190]
theorem svTsv12f2_end : blockEnd sigstoreVerifyCode 0x12F2 svTsv12f2 = some 0x12F6 := by
  simp only [svTsv12f2]
  rw [blockEnd, sv_at_12f2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsv130c : List BInstr :=
  [.aluImm .add a0 sp 0x191, .aluImm .add a1 sp 0x1FC, .aluImm .add a2 x0 0x5F]
theorem svTsv130c_end : blockEnd sigstoreVerifyCode 0x130C svTsv130c = some 0x1316 := by
  simp only [svTsv130c]
  rw [blockEnd, sv_at_130c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1310]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1312]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsv131e : List BInstr :=
  [.aluImm .add a1 sp 0x180]
theorem svTsv131e_end : blockEnd sigstoreVerifyCode 0x131E svTsv131e = some 0x1320 := by
  simp only [svTsv131e]
  rw [blockEnd, sv_at_131e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsv133a : List BInstr :=
  [.aluImm .add a0 (21 : Fin 32) 0x308]
theorem svTsv133a_end : blockEnd sigstoreVerifyCode 0x133A svTsv133a = some 0x133E := by
  simp only [svTsv133a]
  rw [blockEnd, sv_at_133a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsv1340 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x100]
theorem svTsv1340_end : blockEnd sigstoreVerifyCode 0x1340 svTsv1340 = some 0x1344 := by
  simp only [svTsv1340]
  rw [blockEnd, sv_at_1340]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tsv {B out bp x20 x21 x22 x23 x24 x26 x27 : Word} {sr ss : Bytes} {tp tl w4c w48 w44 w50 dg w3c w7c : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x12BE (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (q0_380 : ∀ j, j < 47 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0))
    (q0_3af : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0))
    (h74 : tp ≠ 0) :
    (¬ (True) ∧ SvErrRet B out v n0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1344 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x100 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 ∧
        reg n' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (x21) + BitVec.ofNat 32 0x308 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = tp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x188) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0)) ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0)) ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4), (0x174, 0x1), (0x188, 0x4), (0x18C, 0x4), (0x78, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x12BE
  obtain ⟨n1, c1, u1⟩ := s0.block svTsv12be E0.self svTsv12be_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x12C6 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTsv12be (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_25 : reg n1 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = x27 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1FC := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTsv12be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTsv12be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0x5F := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTsv12be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m1]; exact w0_3c
  have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m1]; exact w0_44
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m1]; exact w0_48
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m1]; exact w0_4c
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m1]; exact w0_64
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m1]; exact w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m1]; exact w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m1]; exact w0_7c
  have q1_380 : ∀ j, j < 47 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m1]; exact q0_380 j hj
  have q1_3af : ∀ j, j < 48 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m1]; exact q0_3af j hj
  -- 0x12C6: memcpy
  obtain ⟨n2, P2, K2, X2⟩ := sv_mc (c := 0x1FC) (d := 0x380) (N := 0x5F) F E1 s1 sv_at_12c6 sv_at_12ca
    (by decide) (by decide) g1_2 g1_10 g1_11 g1_12
    (by decide) (by decide) (by decide)
  have s2 := P2.st
  have fr2 := P2.fr
  have t2 : Steps n0 n2 := t1.trans P2.steps
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [P2.regs sp (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P2.regs (3 : Fin 32) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P2.regs (4 : Fin 32) (by decide), g1_4]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [P2.regs (18 : Fin 32) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [P2.regs (19 : Fin 32) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [P2.regs (20 : Fin 32) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [P2.regs (21 : Fin 32) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [P2.regs (22 : Fin 32) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [P2.regs (23 : Fin 32) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by rw [P2.regs (24 : Fin 32) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [P2.regs (25 : Fin 32) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [P2.regs (26 : Fin 32) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = x27 := by rw [P2.regs (27 : Fin 32) (by decide), g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x1FC, 0x5F)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have w2_3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K2.w32 (by decide) (by decide)).trans w1_3c
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K2.w32 (by decide) (by decide)).trans w1_44
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K2.w32 (by decide) (by decide)).trans w1_48
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K2.w32 (by decide) (by decide)).trans w1_4c
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K2.w32 (by decide) (by decide)).trans w1_50
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K2.w32 (by decide) (by decide)).trans w1_64
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K2.w32 (by decide) (by decide)).trans w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K2.w32 (by decide) (by decide)).trans w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K2.w32 (by decide) (by decide)).trans w1_7c
  have q2_380 : ∀ j, j < 47 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_380 j hj)
  have q2_3af : ∀ j, j < 48 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_3af j hj)
  have q2_1fc : ∀ j, j < 47 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by
    rw [show 0x1FC + j = 0x1FC + (0x0 + j) by omega, X2 (0x0 + j) (by omega),
      show 0x380 + (0x0 + j) = 0x380 + j by omega]; exact q1_380 j (by omega)
  have q2_22b : ∀ j, j < 48 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by
    rw [show 0x22B + j = 0x1FC + (0x2F + j) by omega, X2 (0x2F + j) (by omega),
      show 0x380 + (0x2F + j) = 0x3AF + j by omega]; exact q1_3af j (by omega)
  clear q1_3af q1_380 w1_7c w1_78 w1_74 w1_64 w1_50 w1_4c w1_48 w1_44 w1_3c g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x12CE: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_12ce (off' := 0x12D0) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x12D0 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
  have g3_25 : reg n3 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_10 : reg n3 a0 = tp := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr, w2_74]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x1FC, 0x5F)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_3c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m3]; exact w2_3c
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m3]; exact w2_44
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m3]; exact w2_48
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m3]; exact w2_4c
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m3]; exact w2_64
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m3]; exact w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m3]; exact w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m3]; exact w2_7c
  have q3_1fc : ∀ j, j < 47 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m3]; exact q2_1fc j hj
  have q3_22b : ∀ j, j < 48 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m3]; exact q2_22b j hj
  have q3_380 : ∀ j, j < 47 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m3]; exact q2_380 j hj
  have q3_3af : ∀ j, j < 48 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m3]; exact q2_3af j hj
  clear q2_22b q2_1fc q2_3af q2_380 w2_7c w2_78 w2_74 w2_64 w2_50 w2_4c w2_48 w2_44 w2_3c g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 s2 X2 K2 P2
  -- 0x12D0: branch, not taken
  obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0x12D2 sv_at_12d0
    (by decide) (by rw [g3_10, s3.zero]; exact br_beq_f h74)
  have s4 : St n4.mem SV n4 0x12D2 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
  have g4_10 : reg n4 a0 = tp := by rw [u4.regs, g3_10]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = x24 := by rw [u4.regs, g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u4.regs, g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = x27 := by rw [u4.regs, g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x1FC, 0x5F)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m4]; exact w3_3c
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m4]; exact w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m4]; exact w3_48
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m4]; exact w3_4c
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m4]; exact w3_50
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m4]; exact w3_64
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m4]; exact w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m4]; exact w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m4]; exact w3_7c
  have q4_1fc : ∀ j, j < 47 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m4]; exact q3_1fc j hj
  have q4_22b : ∀ j, j < 48 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m4]; exact q3_22b j hj
  have q4_380 : ∀ j, j < 47 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m4]; exact q3_380 j hj
  have q4_3af : ∀ j, j < 48 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m4]; exact q3_3af j hj
  clear q3_3af q3_380 q3_22b q3_1fc w3_7c w3_78 w3_74 w3_64 w3_50 w3_4c w3_48 w3_44 w3_3c g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x12D2: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_12d2 (off' := 0x12D4) (by decide)
    (by rw [g4_2, show B + 0x21A0 + 0x78 = B + 0x21A0 + BitVec.ofNat 32 0x78 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0x12D4 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_10 : reg n5 a0 = tp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
  have g5_8 : reg n5 (8 : Fin 32) = tl := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_2, show B + 0x21A0 + 0x78 = B + 0x21A0 + BitVec.ofNat 32 0x78 by sv_addr, w4_78]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x1FC, 0x5F)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m5]; exact w4_3c
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m5]; exact w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m5]; exact w4_4c
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m5]; exact w4_64
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m5]; exact w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m5]; exact w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m5]; exact w4_7c
  have q5_1fc : ∀ j, j < 47 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_1fc j hj
  have q5_22b : ∀ j, j < 48 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m5]; exact q4_22b j hj
  have q5_380 : ∀ j, j < 47 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_380 j hj
  have q5_3af : ∀ j, j < 48 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m5]; exact q4_3af j hj
  clear q4_3af q4_380 q4_22b q4_1fc w4_7c w4_78 w4_74 w4_64 w4_50 w4_4c w4_48 w4_44 w4_3c g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0x12D4
  obtain ⟨n6, c6, u6⟩ := s5.block svTsv12d4 E5.self svTsv12d4_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x12E0 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svTsv12d4 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_8 : reg n6 (8 : Fin 32) = tl := by
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
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_10 : reg n6 a0 = (tl) >>> 8 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTsv12d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_10, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_11 : reg n6 a1 = ((tl) >>> 8) >>> 8 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTsv12d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_10, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_12 : reg n6 a2 = ((tl) >>> 8) >>> 16 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTsv12d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_10, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x1FC, 0x5F)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m6]; exact w5_3c
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m6]; exact w5_48
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m6]; exact w5_4c
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m6]; exact w5_64
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m6]; exact w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m6]; exact w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m6]; exact w5_7c
  have q6_1fc : ∀ j, j < 47 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_1fc j hj
  have q6_22b : ∀ j, j < 48 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m6]; exact q5_22b j hj
  have q6_380 : ∀ j, j < 47 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_380 j hj
  have q6_3af : ∀ j, j < 48 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m6]; exact q5_3af j hj
  clear q5_3af q5_380 q5_22b q5_1fc w5_7c w5_78 w5_74 w5_64 w5_50 w5_4c w5_48 w5_44 w5_3c g5_8 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  rw [shr_shr] at g6_11 g6_12
  -- 0x12E0: sb
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := sv_sb F E6 s6 sv_at_12e0 (off' := 0x12E4) (c := 0x175)
    (by decide) (by rw [g6_2]; sv_addr) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = tl := by rw [rg7 (8 : Fin 32), g6_8]
  have g7_10 : reg n7 a0 = (tl) >>> 8 := by rw [rg7 a0, g6_10]
  have g7_11 : reg n7 a1 = (tl) >>> (8 + 8) := by rw [rg7 a1, g6_11]
  have g7_12 : reg n7 a2 = (tl) >>> (8 + 16) := by rw [rg7 a2, g6_12]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rg7 (18 : Fin 32), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rg7 (19 : Fin 32), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [rg7 (20 : Fin 32), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [rg7 (21 : Fin 32), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [rg7 (22 : Fin 32), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [rg7 (23 : Fin 32), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [rg7 (24 : Fin 32), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg7 (25 : Fin 32), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [rg7 (26 : Fin 32), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [rg7 (27 : Fin 32), g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x1FC, 0x5F), (0x175, 0x1)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K7.w32 (by decide) (by decide)).trans w6_3c
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K7.w32 (by decide) (by decide)).trans w6_44
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K7.w32 (by decide) (by decide)).trans w6_48
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K7.w32 (by decide) (by decide)).trans w6_4c
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K7.w32 (by decide) (by decide)).trans w6_50
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K7.w32 (by decide) (by decide)).trans w6_64
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K7.w32 (by decide) (by decide)).trans w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K7.w32 (by decide) (by decide)).trans w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K7.w32 (by decide) (by decide)).trans w6_7c
  have b7_175 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := by rw [W7, g6_10]
  have q7_1fc : ∀ j, j < 47 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K7.range (by decide) (by decide) j hj).trans (q6_1fc j hj)
  have q7_22b : ∀ j, j < 48 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K7.range (by decide) (by decide) j hj).trans (q6_22b j hj)
  have q7_380 : ∀ j, j < 47 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K7.range (by decide) (by decide) j hj).trans (q6_380 j hj)
  have q7_3af : ∀ j, j < 48 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K7.range (by decide) (by decide) j hj).trans (q6_3af j hj)
  clear q6_3af q6_380 q6_22b q6_1fc w6_7c w6_78 w6_74 w6_64 w6_50 w6_4c w6_48 w6_44 w6_3c g6_12 g6_11 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0x12E4: sb
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sb F E7 s7 sv_at_12e4 (off' := 0x12E8) (c := 0x176)
    (by decide) (by rw [g7_2]; sv_addr) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = tl := by rw [rg8 (8 : Fin 32), g7_8]
  have g8_10 : reg n8 a0 = (tl) >>> 8 := by rw [rg8 a0, g7_10]
  have g8_11 : reg n8 a1 = (tl) >>> (8 + 8) := by rw [rg8 a1, g7_11]
  have g8_12 : reg n8 a2 = (tl) >>> (8 + 16) := by rw [rg8 a2, g7_12]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [rg8 (20 : Fin 32), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [rg8 (22 : Fin 32), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [rg8 (23 : Fin 32), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [rg8 (26 : Fin 32), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by rw [rg8 (27 : Fin 32), g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K8.w32 (by decide) (by decide)).trans w7_3c
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K8.w32 (by decide) (by decide)).trans w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K8.w32 (by decide) (by decide)).trans w7_48
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K8.w32 (by decide) (by decide)).trans w7_4c
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K8.w32 (by decide) (by decide)).trans w7_50
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K8.w32 (by decide) (by decide)).trans w7_64
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K8.w32 (by decide) (by decide)).trans w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K8.w32 (by decide) (by decide)).trans w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K8.w32 (by decide) (by decide)).trans w7_7c
  have b8_175 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K8.b8 (by decide) (by decide)).trans b7_175
  have b8_176 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := by rw [W8, g7_11]
  have q8_1fc : ∀ j, j < 47 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_1fc j hj)
  have q8_22b : ∀ j, j < 48 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_22b j hj)
  have q8_380 : ∀ j, j < 47 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_380 j hj)
  have q8_3af : ∀ j, j < 48 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_3af j hj)
  clear q7_3af q7_380 q7_22b q7_1fc b7_175 w7_7c w7_78 w7_74 w7_64 w7_50 w7_4c w7_48 w7_44 w7_3c g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_12 g7_11 g7_10 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0x12E8: sb
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sb F E8 s8 sv_at_12e8 (off' := 0x12EC) (c := 0x177)
    (by decide) (by rw [g8_2]; sv_addr) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = tl := by rw [rg9 (8 : Fin 32), g8_8]
  have g9_10 : reg n9 a0 = (tl) >>> 8 := by rw [rg9 a0, g8_10]
  have g9_11 : reg n9 a1 = (tl) >>> (8 + 8) := by rw [rg9 a1, g8_11]
  have g9_12 : reg n9 a2 = (tl) >>> (8 + 16) := by rw [rg9 a2, g8_12]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rg9 (18 : Fin 32), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rg9 (19 : Fin 32), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [rg9 (20 : Fin 32), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [rg9 (21 : Fin 32), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [rg9 (22 : Fin 32), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [rg9 (23 : Fin 32), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [rg9 (24 : Fin 32), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg9 (25 : Fin 32), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [rg9 (26 : Fin 32), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [rg9 (27 : Fin 32), g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K9.w32 (by decide) (by decide)).trans w8_3c
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K9.w32 (by decide) (by decide)).trans w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K9.w32 (by decide) (by decide)).trans w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K9.w32 (by decide) (by decide)).trans w8_4c
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K9.w32 (by decide) (by decide)).trans w8_50
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K9.w32 (by decide) (by decide)).trans w8_64
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K9.w32 (by decide) (by decide)).trans w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K9.w32 (by decide) (by decide)).trans w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K9.w32 (by decide) (by decide)).trans w8_7c
  have b9_175 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K9.b8 (by decide) (by decide)).trans b8_175
  have b9_176 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := (K9.b8 (by decide) (by decide)).trans b8_176
  have b9_177 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := by rw [W9, g8_12]
  have q9_1fc : ∀ j, j < 47 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_1fc j hj)
  have q9_22b : ∀ j, j < 48 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_22b j hj)
  have q9_380 : ∀ j, j < 47 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_380 j hj)
  have q9_3af : ∀ j, j < 48 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_3af j hj)
  clear q8_3af q8_380 q8_22b q8_1fc b8_176 b8_175 w8_7c w8_78 w8_74 w8_64 w8_50 w8_4c w8_48 w8_44 w8_3c g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_12 g8_11 g8_10 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0x12EC: lw
  obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_12ec (off' := 0x12EE) (by decide)
    (by rw [g9_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s10 : St n10.mem SV n10 0x12EE (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = tl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_8]
  have g10_11 : reg n10 a1 = (tl) >>> (8 + 8) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_11]
  have g10_12 : reg n10 a2 = (tl) >>> (8 + 16) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_12]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
  have g10_10 : reg n10 a0 = w4c := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w9_4c]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m10]; exact w9_3c
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m10]; exact w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m10]; exact w9_4c
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m10]; exact w9_64
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m10]; exact w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m10]; exact w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m10]; exact w9_7c
  have b10_175 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := by rw [m10]; exact b9_175
  have b10_176 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := by rw [m10]; exact b9_176
  have b10_177 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := by rw [m10]; exact b9_177
  have q10_1fc : ∀ j, j < 47 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_1fc j hj
  have q10_22b : ∀ j, j < 48 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m10]; exact q9_22b j hj
  have q10_380 : ∀ j, j < 47 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_380 j hj
  have q10_3af : ∀ j, j < 48 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m10]; exact q9_3af j hj
  clear q9_3af q9_380 q9_22b q9_1fc b9_177 b9_176 b9_175 w9_7c w9_78 w9_74 w9_64 w9_50 w9_4c w9_48 w9_44 w9_3c g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_12 g9_11 g9_10 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  -- 0x12EE: sw
  obtain ⟨n11, d11, s11, fr11, K11, W11, rg11⟩ := sv_sw F E10 s10 sv_at_12ee (off' := 0x12F2) (c := 0x178)
    (by decide) (by rw [g10_2]; sv_addr) (by decide) (by decide)
  have t11 : Steps n0 n11 := t10.trans d11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rg11 sp, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg11 (3 : Fin 32), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg11 (4 : Fin 32), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = tl := by rw [rg11 (8 : Fin 32), g10_8]
  have g11_10 : reg n11 a0 = w4c := by rw [rg11 a0, g10_10]
  have g11_11 : reg n11 a1 = (tl) >>> (8 + 8) := by rw [rg11 a1, g10_11]
  have g11_12 : reg n11 a2 = (tl) >>> (8 + 16) := by rw [rg11 a2, g10_12]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rg11 (18 : Fin 32), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rg11 (19 : Fin 32), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [rg11 (20 : Fin 32), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [rg11 (21 : Fin 32), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [rg11 (22 : Fin 32), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [rg11 (23 : Fin 32), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [rg11 (24 : Fin 32), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg11 (25 : Fin 32), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [rg11 (26 : Fin 32), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [rg11 (27 : Fin 32), g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K11.w32 (by decide) (by decide)).trans w10_3c
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K11.w32 (by decide) (by decide)).trans w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K11.w32 (by decide) (by decide)).trans w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K11.w32 (by decide) (by decide)).trans w10_4c
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K11.w32 (by decide) (by decide)).trans w10_50
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K11.w32 (by decide) (by decide)).trans w10_64
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K11.w32 (by decide) (by decide)).trans w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K11.w32 (by decide) (by decide)).trans w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K11.w32 (by decide) (by decide)).trans w10_7c
  have b11_175 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_175
  have b11_176 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_176
  have b11_177 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_177
  have w11_178 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [W11, g10_10]
  have q11_1fc : ∀ j, j < 47 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_1fc j hj)
  have q11_22b : ∀ j, j < 48 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_22b j hj)
  have q11_380 : ∀ j, j < 47 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_380 j hj)
  have q11_3af : ∀ j, j < 48 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_3af j hj)
  clear q10_3af q10_380 q10_22b q10_1fc b10_177 b10_176 b10_175 w10_7c w10_78 w10_74 w10_64 w10_50 w10_4c w10_48 w10_44 w10_3c g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_12 g10_11 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x12F2
  obtain ⟨n12, c12, u12⟩ := s11.block svTsv12f2 E11.self svTsv12f2_end
    ⟨trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x12F6 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svTsv12f2 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_8 : reg n12 (8 : Fin 32) = tl := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_10 : reg n12 a0 = w4c := by
    rw [rb12, runBlock_reg _ _ _ a0 s11.zero (by decide), g11_10]
  have g12_11 : reg n12 a1 = (tl) >>> (8 + 8) := by
    rw [rb12, runBlock_reg _ _ _ a1 s11.zero (by decide), g11_11]
  have g12_12 : reg n12 a2 = (tl) >>> (8 + 16) := by
    rw [rb12, runBlock_reg _ _ _ a2 s11.zero (by decide), g11_12]
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
  have g12_25 : reg n12 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_26 : reg n12 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svTsv12f2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_10, g11_11, g11_12, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m12]; exact w11_3c
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m12]; exact w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m12]; exact w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m12]; exact w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m12]; exact w11_64
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m12]; exact w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m12]; exact w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m12]; exact w11_7c
  have w12_178 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m12]; exact w11_178
  have b12_175 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := by rw [m12]; exact b11_175
  have b12_176 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := by rw [m12]; exact b11_176
  have b12_177 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := by rw [m12]; exact b11_177
  have q12_1fc : ∀ j, j < 47 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m12]; exact q11_1fc j hj
  have q12_22b : ∀ j, j < 48 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m12]; exact q11_22b j hj
  have q12_380 : ∀ j, j < 47 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m12]; exact q11_380 j hj
  have q12_3af : ∀ j, j < 48 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m12]; exact q11_3af j hj
  clear q11_3af q11_380 q11_22b q11_1fc w11_178 b11_177 b11_176 b11_175 w11_7c w11_78 w11_74 w11_64 w11_50 w11_4c w11_48 w11_44 w11_3c g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_12 g11_11 g11_10 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 rg11 W11 K11 fr11 s11 d11
  -- 0x12F6: lw
  obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_12f6 (off' := 0x12F8) (by decide)
    (by rw [g12_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s13 : St n13.mem SV n13 0x12F8 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = tl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_8]
  have g13_11 : reg n13 a1 = (tl) >>> (8 + 8) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_11]
  have g13_12 : reg n13 a2 = (tl) >>> (8 + 16) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_12]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
  have g13_10 : reg n13 a0 = w48 := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w12_48]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m13]; exact w12_3c
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m13]; exact w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m13]; exact w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m13]; exact w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m13]; exact w12_64
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m13]; exact w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m13]; exact w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m13]; exact w12_7c
  have w13_178 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m13]; exact w12_178
  have b13_175 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := by rw [m13]; exact b12_175
  have b13_176 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := by rw [m13]; exact b12_176
  have b13_177 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := by rw [m13]; exact b12_177
  have q13_1fc : ∀ j, j < 47 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m13]; exact q12_1fc j hj
  have q13_22b : ∀ j, j < 48 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m13]; exact q12_22b j hj
  have q13_380 : ∀ j, j < 47 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m13]; exact q12_380 j hj
  have q13_3af : ∀ j, j < 48 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m13]; exact q12_3af j hj
  clear q12_3af q12_380 q12_22b q12_1fc b12_177 b12_176 b12_175 w12_178 w12_7c w12_78 w12_74 w12_64 w12_50 w12_4c w12_48 w12_44 w12_3c g12_26 g12_27 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_12 g12_11 g12_10 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x12F8: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_12f8 (off' := 0x12FC) (c := 0x17C)
    (by decide) (by rw [g13_2]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = tl := by rw [rg14 (8 : Fin 32), g13_8]
  have g14_10 : reg n14 a0 = w48 := by rw [rg14 a0, g13_10]
  have g14_11 : reg n14 a1 = (tl) >>> (8 + 8) := by rw [rg14 a1, g13_11]
  have g14_12 : reg n14 a2 = (tl) >>> (8 + 16) := by rw [rg14 a2, g13_12]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [rg14 (20 : Fin 32), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [rg14 (23 : Fin 32), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K14.w32 (by decide) (by decide)).trans w13_3c
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K14.w32 (by decide) (by decide)).trans w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K14.w32 (by decide) (by decide)).trans w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K14.w32 (by decide) (by decide)).trans w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K14.w32 (by decide) (by decide)).trans w13_50
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K14.w32 (by decide) (by decide)).trans w13_64
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K14.w32 (by decide) (by decide)).trans w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K14.w32 (by decide) (by decide)).trans w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K14.w32 (by decide) (by decide)).trans w13_7c
  have w14_178 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K14.w32 (by decide) (by decide)).trans w13_178
  have b14_175 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K14.b8 (by decide) (by decide)).trans b13_175
  have b14_176 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := (K14.b8 (by decide) (by decide)).trans b13_176
  have b14_177 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := (K14.b8 (by decide) (by decide)).trans b13_177
  have w14_17c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := by rw [W14, g13_10]
  have q14_1fc : ∀ j, j < 47 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_1fc j hj)
  have q14_22b : ∀ j, j < 48 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_22b j hj)
  have q14_380 : ∀ j, j < 47 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_380 j hj)
  have q14_3af : ∀ j, j < 48 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_3af j hj)
  clear q13_3af q13_380 q13_22b q13_1fc b13_177 b13_176 b13_175 w13_178 w13_7c w13_78 w13_74 w13_64 w13_50 w13_4c w13_48 w13_44 w13_3c g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_12 g13_11 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0x12FC: lw
  obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_12fc (off' := 0x12FE) (by decide)
    (by rw [g14_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s15 : St n15.mem SV n15 0x12FE (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = tl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_8]
  have g15_11 : reg n15 a1 = (tl) >>> (8 + 8) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_11]
  have g15_12 : reg n15 a2 = (tl) >>> (8 + 16) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_12]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_10 : reg n15 a0 = w44 := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w14_44]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m15]; exact w14_3c
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m15]; exact w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m15]; exact w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m15]; exact w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m15]; exact w14_50
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m15]; exact w14_64
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m15]; exact w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m15]; exact w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m15]; exact w14_7c
  have w15_178 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m15]; exact w14_178
  have w15_17c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := by rw [m15]; exact w14_17c
  have b15_175 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := by rw [m15]; exact b14_175
  have b15_176 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := by rw [m15]; exact b14_176
  have b15_177 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := by rw [m15]; exact b14_177
  have q15_1fc : ∀ j, j < 47 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m15]; exact q14_1fc j hj
  have q15_22b : ∀ j, j < 48 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m15]; exact q14_22b j hj
  have q15_380 : ∀ j, j < 47 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m15]; exact q14_380 j hj
  have q15_3af : ∀ j, j < 48 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m15]; exact q14_3af j hj
  clear q14_3af q14_380 q14_22b q14_1fc w14_17c b14_177 b14_176 b14_175 w14_178 w14_7c w14_78 w14_74 w14_64 w14_50 w14_4c w14_48 w14_44 w14_3c g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_12 g14_11 g14_10 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0x12FE: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_12fe (off' := 0x1302) (c := 0x180)
    (by decide) (by rw [g15_2]; sv_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = tl := by rw [rg16 (8 : Fin 32), g15_8]
  have g16_10 : reg n16 a0 = w44 := by rw [rg16 a0, g15_10]
  have g16_11 : reg n16 a1 = (tl) >>> (8 + 8) := by rw [rg16 a1, g15_11]
  have g16_12 : reg n16 a2 = (tl) >>> (8 + 16) := by rw [rg16 a2, g15_12]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [rg16 (20 : Fin 32), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [rg16 (21 : Fin 32), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [rg16 (22 : Fin 32), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [rg16 (23 : Fin 32), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [rg16 (24 : Fin 32), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg16 (25 : Fin 32), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg16 (26 : Fin 32), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = x27 := by rw [rg16 (27 : Fin 32), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K16.w32 (by decide) (by decide)).trans w15_3c
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K16.w32 (by decide) (by decide)).trans w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K16.w32 (by decide) (by decide)).trans w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K16.w32 (by decide) (by decide)).trans w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K16.w32 (by decide) (by decide)).trans w15_50
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K16.w32 (by decide) (by decide)).trans w15_64
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K16.w32 (by decide) (by decide)).trans w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K16.w32 (by decide) (by decide)).trans w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K16.w32 (by decide) (by decide)).trans w15_7c
  have w16_178 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K16.w32 (by decide) (by decide)).trans w15_178
  have w16_17c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := (K16.w32 (by decide) (by decide)).trans w15_17c
  have b16_175 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K16.b8 (by decide) (by decide)).trans b15_175
  have b16_176 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := (K16.b8 (by decide) (by decide)).trans b15_176
  have b16_177 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := (K16.b8 (by decide) (by decide)).trans b15_177
  have w16_180 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := by rw [W16, g15_10]
  have q16_1fc : ∀ j, j < 47 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_1fc j hj)
  have q16_22b : ∀ j, j < 48 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_22b j hj)
  have q16_380 : ∀ j, j < 47 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_380 j hj)
  have q16_3af : ∀ j, j < 48 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_3af j hj)
  clear q15_3af q15_380 q15_22b q15_1fc b15_177 b15_176 b15_175 w15_17c w15_178 w15_7c w15_78 w15_74 w15_64 w15_50 w15_4c w15_48 w15_44 w15_3c g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_12 g15_11 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0x1302: lw
  obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_1302 (off' := 0x1304) (by decide)
    (by rw [g16_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s17 : St n17.mem SV n17 0x1304 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = tl := by rw [u17.regs, upd_ne (by decide) (by decide), g16_8]
  have g17_11 : reg n17 a1 = (tl) >>> (8 + 8) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_11]
  have g17_12 : reg n17 a2 = (tl) >>> (8 + 16) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_12]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
  have g17_10 : reg n17 a0 = w50 := by
    rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g16_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w16_50]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m17]; exact w16_3c
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m17]; exact w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m17]; exact w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m17]; exact w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m17]; exact w16_64
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m17]; exact w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m17]; exact w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m17]; exact w16_7c
  have w17_178 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m17]; exact w16_178
  have w17_17c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := by rw [m17]; exact w16_17c
  have w17_180 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := by rw [m17]; exact w16_180
  have b17_175 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := by rw [m17]; exact b16_175
  have b17_176 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := by rw [m17]; exact b16_176
  have b17_177 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := by rw [m17]; exact b16_177
  have q17_1fc : ∀ j, j < 47 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m17]; exact q16_1fc j hj
  have q17_22b : ∀ j, j < 48 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m17]; exact q16_22b j hj
  have q17_380 : ∀ j, j < 47 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m17]; exact q16_380 j hj
  have q17_3af : ∀ j, j < 48 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m17]; exact q16_3af j hj
  clear q16_3af q16_380 q16_22b q16_1fc w16_180 b16_177 b16_176 b16_175 w16_17c w16_178 w16_7c w16_78 w16_74 w16_64 w16_50 w16_4c w16_48 w16_44 w16_3c g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_12 g16_11 g16_10 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0x1304: sw
  obtain ⟨n18, d18, s18, fr18, K18, W18, rg18⟩ := sv_sw F E17 s17 sv_at_1304 (off' := 0x1308) (c := 0x184)
    (by decide) (by rw [g17_2]; sv_addr) (by decide) (by decide)
  have t18 : Steps n0 n18 := t17.trans d18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [rg18 sp, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg18 (3 : Fin 32), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg18 (4 : Fin 32), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = tl := by rw [rg18 (8 : Fin 32), g17_8]
  have g18_10 : reg n18 a0 = w50 := by rw [rg18 a0, g17_10]
  have g18_11 : reg n18 a1 = (tl) >>> (8 + 8) := by rw [rg18 a1, g17_11]
  have g18_12 : reg n18 a2 = (tl) >>> (8 + 16) := by rw [rg18 a2, g17_12]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [rg18 (18 : Fin 32), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [rg18 (19 : Fin 32), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [rg18 (20 : Fin 32), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [rg18 (21 : Fin 32), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [rg18 (22 : Fin 32), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [rg18 (23 : Fin 32), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [rg18 (24 : Fin 32), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg18 (25 : Fin 32), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg18 (26 : Fin 32), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [rg18 (27 : Fin 32), g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K18.w32 (by decide) (by decide)).trans w17_3c
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K18.w32 (by decide) (by decide)).trans w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K18.w32 (by decide) (by decide)).trans w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K18.w32 (by decide) (by decide)).trans w17_4c
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K18.w32 (by decide) (by decide)).trans w17_50
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K18.w32 (by decide) (by decide)).trans w17_64
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K18.w32 (by decide) (by decide)).trans w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K18.w32 (by decide) (by decide)).trans w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K18.w32 (by decide) (by decide)).trans w17_7c
  have w18_178 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K18.w32 (by decide) (by decide)).trans w17_178
  have w18_17c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := (K18.w32 (by decide) (by decide)).trans w17_17c
  have w18_180 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := (K18.w32 (by decide) (by decide)).trans w17_180
  have b18_175 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_175
  have b18_176 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_176
  have b18_177 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_177
  have w18_184 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := by rw [W18, g17_10]
  have q18_1fc : ∀ j, j < 47 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_1fc j hj)
  have q18_22b : ∀ j, j < 48 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_22b j hj)
  have q18_380 : ∀ j, j < 47 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_380 j hj)
  have q18_3af : ∀ j, j < 48 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_3af j hj)
  clear q17_3af q17_380 q17_22b q17_1fc b17_177 b17_176 b17_175 w17_180 w17_17c w17_178 w17_7c w17_78 w17_74 w17_64 w17_50 w17_4c w17_48 w17_44 w17_3c g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_12 g17_11 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0x1308: sb
  obtain ⟨n19, d19, s19, fr19, K19, W19, rg19⟩ := sv_sb F E18 s18 sv_at_1308 (off' := 0x130C) (c := 0x190)
    (by decide) (by rw [g18_2]; sv_addr) (by decide)
  have t19 : Steps n0 n19 := t18.trans d19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keep K19 (by decide)
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [rg19 sp, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg19 (3 : Fin 32), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg19 (4 : Fin 32), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = tl := by rw [rg19 (8 : Fin 32), g18_8]
  have g19_10 : reg n19 a0 = w50 := by rw [rg19 a0, g18_10]
  have g19_11 : reg n19 a1 = (tl) >>> (8 + 8) := by rw [rg19 a1, g18_11]
  have g19_12 : reg n19 a2 = (tl) >>> (8 + 16) := by rw [rg19 a2, g18_12]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rg19 (18 : Fin 32), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rg19 (19 : Fin 32), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [rg19 (20 : Fin 32), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [rg19 (21 : Fin 32), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [rg19 (22 : Fin 32), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [rg19 (23 : Fin 32), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [rg19 (24 : Fin 32), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg19 (25 : Fin 32), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg19 (26 : Fin 32), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [rg19 (27 : Fin 32), g18_27]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1)] := keep_kk18.trans K19.toL
  clear keep_kk18
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K19.w32 (by decide) (by decide)).trans w18_3c
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K19.w32 (by decide) (by decide)).trans w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K19.w32 (by decide) (by decide)).trans w18_48
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K19.w32 (by decide) (by decide)).trans w18_4c
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K19.w32 (by decide) (by decide)).trans w18_50
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K19.w32 (by decide) (by decide)).trans w18_64
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K19.w32 (by decide) (by decide)).trans w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K19.w32 (by decide) (by decide)).trans w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K19.w32 (by decide) (by decide)).trans w18_7c
  have w19_178 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K19.w32 (by decide) (by decide)).trans w18_178
  have w19_17c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := (K19.w32 (by decide) (by decide)).trans w18_17c
  have w19_180 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := (K19.w32 (by decide) (by decide)).trans w18_180
  have w19_184 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := (K19.w32 (by decide) (by decide)).trans w18_184
  have b19_175 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_175
  have b19_176 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_176
  have b19_177 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_177
  have b19_190 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [W19, g18_25, lbu_low]
  have q19_1fc : ∀ j, j < 47 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K19.range (by decide) (by decide) j hj).trans (q18_1fc j hj)
  have q19_22b : ∀ j, j < 48 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K19.range (by decide) (by decide) j hj).trans (q18_22b j hj)
  have q19_380 : ∀ j, j < 47 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K19.range (by decide) (by decide) j hj).trans (q18_380 j hj)
  have q19_3af : ∀ j, j < 48 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K19.range (by decide) (by decide) j hj).trans (q18_3af j hj)
  clear q18_3af q18_380 q18_22b q18_1fc w18_184 b18_177 b18_176 b18_175 w18_180 w18_17c w18_178 w18_7c w18_78 w18_74 w18_64 w18_50 w18_4c w18_48 w18_44 w18_3c g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_12 g18_11 g18_10 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 rg18 W18 K18 fr18 s18 d18
  -- 0x130C
  obtain ⟨n20, c20, u20⟩ := s19.block svTsv130c E19.self svTsv130c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x1316 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svTsv130c (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = tl := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
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
  have g20_25 : reg n20 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0x191 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svTsv130c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_10, g19_11, g19_12, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_11 : reg n20 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1FC := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svTsv130c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_10, g19_11, g19_12, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_12 : reg n20 a2 = BitVec.ofNat 32 0x5F := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svTsv130c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_10, g19_11, g19_12, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m20]; exact w19_3c
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m20]; exact w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m20]; exact w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m20]; exact w19_4c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m20]; exact w19_64
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m20]; exact w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m20]; exact w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m20]; exact w19_7c
  have w20_178 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m20]; exact w19_178
  have w20_17c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := by rw [m20]; exact w19_17c
  have w20_180 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := by rw [m20]; exact w19_180
  have w20_184 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := by rw [m20]; exact w19_184
  have b20_175 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := by rw [m20]; exact b19_175
  have b20_176 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := by rw [m20]; exact b19_176
  have b20_177 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := by rw [m20]; exact b19_177
  have b20_190 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m20]; exact b19_190
  have q20_1fc : ∀ j, j < 47 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m20]; exact q19_1fc j hj
  have q20_22b : ∀ j, j < 48 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m20]; exact q19_22b j hj
  have q20_380 : ∀ j, j < 47 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m20]; exact q19_380 j hj
  have q20_3af : ∀ j, j < 48 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m20]; exact q19_3af j hj
  clear q19_3af q19_380 q19_22b q19_1fc b19_190 b19_177 b19_176 b19_175 w19_184 w19_180 w19_17c w19_178 w19_7c w19_78 w19_74 w19_64 w19_50 w19_4c w19_48 w19_44 w19_3c g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_12 g19_11 g19_10 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 rg19 W19 K19 fr19 s19 d19
  -- 0x1316: memcpy
  obtain ⟨n21, P21, K21, X21⟩ := sv_mc (c := 0x191) (d := 0x1FC) (N := 0x5F) F E20 s20 sv_at_1316 sv_at_131a
    (by decide) (by decide) g20_2 g20_10 g20_11 g20_12
    (by decide) (by decide) (by decide)
  have s21 := P21.st
  have fr21 := P21.fr
  have t21 : Steps n0 n21 := t20.trans P21.steps
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keep K21 (by decide)
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [P21.regs sp (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P21.regs (3 : Fin 32) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P21.regs (4 : Fin 32) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = tl := by rw [P21.regs (8 : Fin 32) (by decide), g20_8]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [P21.regs (18 : Fin 32) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [P21.regs (19 : Fin 32) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [P21.regs (20 : Fin 32) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [P21.regs (21 : Fin 32) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [P21.regs (22 : Fin 32) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [P21.regs (23 : Fin 32) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [P21.regs (24 : Fin 32) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [P21.regs (25 : Fin 32) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [P21.regs (26 : Fin 32) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [P21.regs (27 : Fin 32) (by decide), g20_27]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F)] := keep_kk20.trans K21.toL
  clear keep_kk20
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K21.w32 (by decide) (by decide)).trans w20_3c
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K21.w32 (by decide) (by decide)).trans w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K21.w32 (by decide) (by decide)).trans w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K21.w32 (by decide) (by decide)).trans w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K21.w32 (by decide) (by decide)).trans w20_50
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K21.w32 (by decide) (by decide)).trans w20_64
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K21.w32 (by decide) (by decide)).trans w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K21.w32 (by decide) (by decide)).trans w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K21.w32 (by decide) (by decide)).trans w20_7c
  have w21_178 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K21.w32 (by decide) (by decide)).trans w20_178
  have w21_17c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := (K21.w32 (by decide) (by decide)).trans w20_17c
  have w21_180 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := (K21.w32 (by decide) (by decide)).trans w20_180
  have w21_184 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := (K21.w32 (by decide) (by decide)).trans w20_184
  have b21_175 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K21.b8 (by decide) (by decide)).trans b20_175
  have b21_176 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := (K21.b8 (by decide) (by decide)).trans b20_176
  have b21_177 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := (K21.b8 (by decide) (by decide)).trans b20_177
  have b21_190 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := (K21.b8 (by decide) (by decide)).trans b20_190
  have q21_1fc : ∀ j, j < 47 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K21.range (by decide) (by decide) j hj).trans (q20_1fc j hj)
  have q21_22b : ∀ j, j < 48 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K21.range (by decide) (by decide) j hj).trans (q20_22b j hj)
  have q21_380 : ∀ j, j < 47 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K21.range (by decide) (by decide) j hj).trans (q20_380 j hj)
  have q21_3af : ∀ j, j < 48 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K21.range (by decide) (by decide) j hj).trans (q20_3af j hj)
  have q21_191 : ∀ j, j < 47 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by
    rw [show 0x191 + j = 0x191 + (0x0 + j) by omega, X21 (0x0 + j) (by omega),
      show 0x1FC + (0x0 + j) = 0x1FC + j by omega]; exact q20_1fc j (by omega)
  have q21_1c0 : ∀ j, j < 48 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by
    rw [show 0x1C0 + j = 0x191 + (0x2F + j) by omega, X21 (0x2F + j) (by omega),
      show 0x1FC + (0x2F + j) = 0x22B + j by omega]; exact q20_22b j (by omega)
  clear q20_3af q20_380 q20_22b q20_1fc b20_190 b20_177 b20_176 b20_175 w20_184 w20_180 w20_17c w20_178 w20_7c w20_78 w20_74 w20_64 w20_50 w20_4c w20_48 w20_44 w20_3c g20_12 g20_11 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x131E
  obtain ⟨n22, c22, u22⟩ := s21.block svTsv131e E21.self svTsv131e_end
    ⟨trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem SV n22 0x1320 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock svTsv131e (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
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
  have g22_8 : reg n22 (8 : Fin 32) = tl := by
    rw [rb22, runBlock_reg _ _ _ (8 : Fin 32) s21.zero (by decide), g21_8]
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
  have g22_25 : reg n22 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb22, runBlock_reg _ _ _ (25 : Fin 32) s21.zero (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_11 : reg n22 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svTsv131e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m22]; exact w21_3c
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m22]; exact w21_48
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m22]; exact w21_4c
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m22]; exact w21_50
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m22]; exact w21_64
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m22]; exact w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m22]; exact w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m22]; exact w21_7c
  have w22_178 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m22]; exact w21_178
  have w22_17c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := by rw [m22]; exact w21_17c
  have w22_180 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := by rw [m22]; exact w21_180
  have w22_184 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := by rw [m22]; exact w21_184
  have b22_175 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := by rw [m22]; exact b21_175
  have b22_176 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := by rw [m22]; exact b21_176
  have b22_177 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := by rw [m22]; exact b21_177
  have b22_190 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m22]; exact b21_190
  have q22_191 : ∀ j, j < 47 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m22]; exact q21_191 j hj
  have q22_1c0 : ∀ j, j < 48 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m22]; exact q21_1c0 j hj
  have q22_1fc : ∀ j, j < 47 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m22]; exact q21_1fc j hj
  have q22_22b : ∀ j, j < 48 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m22]; exact q21_22b j hj
  have q22_380 : ∀ j, j < 47 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m22]; exact q21_380 j hj
  have q22_3af : ∀ j, j < 48 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m22]; exact q21_3af j hj
  clear q21_1c0 q21_191 q21_3af q21_380 q21_22b q21_1fc b21_190 b21_177 b21_176 b21_175 w21_184 w21_180 w21_17c w21_178 w21_7c w21_78 w21_74 w21_64 w21_50 w21_4c w21_48 w21_44 w21_3c g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 s21 X21 K21 P21
  -- 0x1320: sw
  obtain ⟨n23, d23, s23, fr23, K23, W23, rg23⟩ := sv_sw F E22 s22 sv_at_1320 (off' := 0x1324) (c := 0x1F0)
    (by decide) (by rw [g22_11]; sv_addr) (by decide) (by decide)
  have t23 : Steps n0 n23 := t22.trans d23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.keep K23 (by decide)
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [rg23 sp, g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg23 (3 : Fin 32), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg23 (4 : Fin 32), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = tl := by rw [rg23 (8 : Fin 32), g22_8]
  have g23_11 : reg n23 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by rw [rg23 a1, g22_11]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [rg23 (18 : Fin 32), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [rg23 (19 : Fin 32), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [rg23 (20 : Fin 32), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [rg23 (21 : Fin 32), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [rg23 (22 : Fin 32), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [rg23 (23 : Fin 32), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = x24 := by rw [rg23 (24 : Fin 32), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg23 (25 : Fin 32), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg23 (26 : Fin 32), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [rg23 (27 : Fin 32), g22_27]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4)] := keep_kk22.trans K23.toL
  clear keep_kk22
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K23.w32 (by decide) (by decide)).trans w22_3c
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K23.w32 (by decide) (by decide)).trans w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K23.w32 (by decide) (by decide)).trans w22_48
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K23.w32 (by decide) (by decide)).trans w22_4c
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K23.w32 (by decide) (by decide)).trans w22_50
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K23.w32 (by decide) (by decide)).trans w22_64
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K23.w32 (by decide) (by decide)).trans w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K23.w32 (by decide) (by decide)).trans w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K23.w32 (by decide) (by decide)).trans w22_7c
  have w23_178 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K23.w32 (by decide) (by decide)).trans w22_178
  have w23_17c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := (K23.w32 (by decide) (by decide)).trans w22_17c
  have w23_180 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := (K23.w32 (by decide) (by decide)).trans w22_180
  have w23_184 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := (K23.w32 (by decide) (by decide)).trans w22_184
  have b23_175 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K23.b8 (by decide) (by decide)).trans b22_175
  have b23_176 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := (K23.b8 (by decide) (by decide)).trans b22_176
  have b23_177 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := (K23.b8 (by decide) (by decide)).trans b22_177
  have b23_190 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := (K23.b8 (by decide) (by decide)).trans b22_190
  have w23_1f0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := by rw [W23, g22_27]
  have q23_191 : ∀ j, j < 47 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_191 j hj)
  have q23_1c0 : ∀ j, j < 48 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_1c0 j hj)
  have q23_1fc : ∀ j, j < 47 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_1fc j hj)
  have q23_22b : ∀ j, j < 48 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_22b j hj)
  have q23_380 : ∀ j, j < 47 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_380 j hj)
  have q23_3af : ∀ j, j < 48 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_3af j hj)
  clear q22_3af q22_380 q22_22b q22_1fc q22_1c0 q22_191 b22_190 b22_177 b22_176 b22_175 w22_184 w22_180 w22_17c w22_178 w22_7c w22_78 w22_74 w22_64 w22_50 w22_4c w22_48 w22_44 w22_3c g22_11 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  -- 0x1324: lw
  obtain ⟨n24, d24, u24⟩ := s23.lw E23.self sv_at_1324 (off' := 0x1326) (by decide)
    (by rw [g23_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s24 : St n24.mem SV n24 0x1326 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = tl := by rw [u24.regs, upd_ne (by decide) (by decide), g23_8]
  have g24_11 : reg n24 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_11]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, upd_ne (by decide) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = x24 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_27]
  have g24_10 : reg n24 a0 = dg := by
    rw [u24.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g23_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr, w23_64]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m24]; exact w23_3c
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m24]; exact w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m24]; exact w23_48
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m24]; exact w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m24]; exact w23_64
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m24]; exact w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m24]; exact w23_7c
  have w24_178 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m24]; exact w23_178
  have w24_17c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := by rw [m24]; exact w23_17c
  have w24_180 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := by rw [m24]; exact w23_180
  have w24_184 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := by rw [m24]; exact w23_184
  have w24_1f0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := by rw [m24]; exact w23_1f0
  have b24_175 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := by rw [m24]; exact b23_175
  have b24_176 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := by rw [m24]; exact b23_176
  have b24_177 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := by rw [m24]; exact b23_177
  have b24_190 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m24]; exact b23_190
  have q24_191 : ∀ j, j < 47 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m24]; exact q23_191 j hj
  have q24_1c0 : ∀ j, j < 48 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m24]; exact q23_1c0 j hj
  have q24_1fc : ∀ j, j < 47 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m24]; exact q23_1fc j hj
  have q24_22b : ∀ j, j < 48 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m24]; exact q23_22b j hj
  have q24_380 : ∀ j, j < 47 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m24]; exact q23_380 j hj
  have q24_3af : ∀ j, j < 48 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m24]; exact q23_3af j hj
  clear q23_3af q23_380 q23_22b q23_1fc q23_1c0 q23_191 w23_1f0 b23_190 b23_177 b23_176 b23_175 w23_184 w23_180 w23_17c w23_178 w23_7c w23_78 w23_74 w23_64 w23_50 w23_4c w23_48 w23_44 w23_3c g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_11 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 rg23 W23 K23 fr23 s23 d23
  -- 0x1326: sw
  obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_1326 (off' := 0x1328) (c := 0x1F4)
    (by decide) (by rw [g24_11]; sv_addr) (by decide) (by decide)
  have t25 : Steps n0 n25 := t24.trans d25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = tl := by rw [rg25 (8 : Fin 32), g24_8]
  have g25_10 : reg n25 a0 = dg := by rw [rg25 a0, g24_10]
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by rw [rg25 a1, g24_11]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [rg25 (20 : Fin 32), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rg25 (21 : Fin 32), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [rg25 (22 : Fin 32), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [rg25 (23 : Fin 32), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = x24 := by rw [rg25 (24 : Fin 32), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg25 (25 : Fin 32), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg25 (26 : Fin 32), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = x27 := by rw [rg25 (27 : Fin 32), g24_27]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4)] := keep_kk24.trans K25.toL
  clear keep_kk24
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K25.w32 (by decide) (by decide)).trans w24_3c
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K25.w32 (by decide) (by decide)).trans w24_44
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K25.w32 (by decide) (by decide)).trans w24_48
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K25.w32 (by decide) (by decide)).trans w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K25.w32 (by decide) (by decide)).trans w24_50
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K25.w32 (by decide) (by decide)).trans w24_64
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K25.w32 (by decide) (by decide)).trans w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K25.w32 (by decide) (by decide)).trans w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K25.w32 (by decide) (by decide)).trans w24_7c
  have w25_178 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K25.w32 (by decide) (by decide)).trans w24_178
  have w25_17c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := (K25.w32 (by decide) (by decide)).trans w24_17c
  have w25_180 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := (K25.w32 (by decide) (by decide)).trans w24_180
  have w25_184 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := (K25.w32 (by decide) (by decide)).trans w24_184
  have w25_1f0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := (K25.w32 (by decide) (by decide)).trans w24_1f0
  have b25_175 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_175
  have b25_176 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_176
  have b25_177 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_177
  have b25_190 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := (K25.b8 (by decide) (by decide)).trans b24_190
  have w25_1f4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg := by rw [W25, g24_10]
  have q25_191 : ∀ j, j < 47 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_191 j hj)
  have q25_1c0 : ∀ j, j < 48 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_1c0 j hj)
  have q25_1fc : ∀ j, j < 47 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_1fc j hj)
  have q25_22b : ∀ j, j < 48 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_22b j hj)
  have q25_380 : ∀ j, j < 47 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_380 j hj)
  have q25_3af : ∀ j, j < 48 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_3af j hj)
  clear q24_3af q24_380 q24_22b q24_1fc q24_1c0 q24_191 b24_190 b24_177 b24_176 b24_175 w24_1f0 w24_184 w24_180 w24_17c w24_178 w24_7c w24_78 w24_74 w24_64 w24_50 w24_4c w24_48 w24_44 w24_3c g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_11 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x1328: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_1328 (off' := 0x132A) (by decide)
    (by rw [g25_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0x132A (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = tl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
  have g26_11 : reg n26 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_11]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_10 : reg n26 a0 = tp := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr, w25_74]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m26]; exact w25_3c
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m26]; exact w25_44
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m26]; exact w25_48
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m26]; exact w25_4c
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m26]; exact w25_50
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m26]; exact w25_64
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m26]; exact w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m26]; exact w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m26]; exact w25_7c
  have w26_178 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m26]; exact w25_178
  have w26_17c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := by rw [m26]; exact w25_17c
  have w26_180 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := by rw [m26]; exact w25_180
  have w26_184 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := by rw [m26]; exact w25_184
  have w26_1f0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := by rw [m26]; exact w25_1f0
  have w26_1f4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg := by rw [m26]; exact w25_1f4
  have b26_175 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := by rw [m26]; exact b25_175
  have b26_176 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := by rw [m26]; exact b25_176
  have b26_177 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := by rw [m26]; exact b25_177
  have b26_190 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m26]; exact b25_190
  have q26_191 : ∀ j, j < 47 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m26]; exact q25_191 j hj
  have q26_1c0 : ∀ j, j < 48 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m26]; exact q25_1c0 j hj
  have q26_1fc : ∀ j, j < 47 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m26]; exact q25_1fc j hj
  have q26_22b : ∀ j, j < 48 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m26]; exact q25_22b j hj
  have q26_380 : ∀ j, j < 47 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m26]; exact q25_380 j hj
  have q26_3af : ∀ j, j < 48 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m26]; exact q25_3af j hj
  clear q25_3af q25_380 q25_22b q25_1fc q25_1c0 q25_191 w25_1f4 b25_190 b25_177 b25_176 b25_175 w25_1f0 w25_184 w25_180 w25_17c w25_178 w25_7c w25_78 w25_74 w25_64 w25_50 w25_4c w25_48 w25_44 w25_3c g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_11 g25_10 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
  -- 0x132A: sw
  obtain ⟨n27, d27, s27, fr27, K27, W27, rg27⟩ := sv_sw F E26 s26 sv_at_132a (off' := 0x132E) (c := 0x170)
    (by decide) (by rw [g26_2]; sv_addr) (by decide) (by decide)
  have t27 : Steps n0 n27 := t26.trans d27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keep K27 (by decide)
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rg27 sp, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg27 (3 : Fin 32), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg27 (4 : Fin 32), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = tl := by rw [rg27 (8 : Fin 32), g26_8]
  have g27_10 : reg n27 a0 = tp := by rw [rg27 a0, g26_10]
  have g27_11 : reg n27 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by rw [rg27 a1, g26_11]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rg27 (18 : Fin 32), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rg27 (19 : Fin 32), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [rg27 (20 : Fin 32), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [rg27 (21 : Fin 32), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [rg27 (22 : Fin 32), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [rg27 (23 : Fin 32), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [rg27 (24 : Fin 32), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg27 (25 : Fin 32), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg27 (26 : Fin 32), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [rg27 (27 : Fin 32), g26_27]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4)] := keep_kk26.trans K27.toL
  clear keep_kk26
  have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K27.w32 (by decide) (by decide)).trans w26_3c
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K27.w32 (by decide) (by decide)).trans w26_44
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K27.w32 (by decide) (by decide)).trans w26_48
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K27.w32 (by decide) (by decide)).trans w26_4c
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K27.w32 (by decide) (by decide)).trans w26_50
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K27.w32 (by decide) (by decide)).trans w26_64
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K27.w32 (by decide) (by decide)).trans w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K27.w32 (by decide) (by decide)).trans w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K27.w32 (by decide) (by decide)).trans w26_7c
  have w27_178 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K27.w32 (by decide) (by decide)).trans w26_178
  have w27_17c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := (K27.w32 (by decide) (by decide)).trans w26_17c
  have w27_180 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := (K27.w32 (by decide) (by decide)).trans w26_180
  have w27_184 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := (K27.w32 (by decide) (by decide)).trans w26_184
  have w27_1f0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := (K27.w32 (by decide) (by decide)).trans w26_1f0
  have w27_1f4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg := (K27.w32 (by decide) (by decide)).trans w26_1f4
  have b27_175 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_175
  have b27_176 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_176
  have b27_177 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_177
  have b27_190 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := (K27.b8 (by decide) (by decide)).trans b26_190
  have w27_170 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = tp := by rw [W27, g26_10]
  have q27_191 : ∀ j, j < 47 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_191 j hj)
  have q27_1c0 : ∀ j, j < 48 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_1c0 j hj)
  have q27_1fc : ∀ j, j < 47 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_1fc j hj)
  have q27_22b : ∀ j, j < 48 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_22b j hj)
  have q27_380 : ∀ j, j < 47 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_380 j hj)
  have q27_3af : ∀ j, j < 48 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_3af j hj)
  clear q26_3af q26_380 q26_22b q26_1fc q26_1c0 q26_191 b26_190 b26_177 b26_176 b26_175 w26_1f4 w26_1f0 w26_184 w26_180 w26_17c w26_178 w26_7c w26_78 w26_74 w26_64 w26_50 w26_4c w26_48 w26_44 w26_3c g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_11 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0x132E: sb
  obtain ⟨n28, d28, s28, fr28, K28, W28, rg28⟩ := sv_sb F E27 s27 sv_at_132e (off' := 0x1332) (c := 0x174)
    (by decide) (by rw [g27_2]; sv_addr) (by decide)
  have t28 : Steps n0 n28 := t27.trans d28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keep K28 (by decide)
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rg28 sp, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg28 (3 : Fin 32), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg28 (4 : Fin 32), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = tl := by rw [rg28 (8 : Fin 32), g27_8]
  have g28_10 : reg n28 a0 = tp := by rw [rg28 a0, g27_10]
  have g28_11 : reg n28 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by rw [rg28 a1, g27_11]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rg28 (18 : Fin 32), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rg28 (19 : Fin 32), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [rg28 (20 : Fin 32), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [rg28 (21 : Fin 32), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [rg28 (22 : Fin 32), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [rg28 (23 : Fin 32), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [rg28 (24 : Fin 32), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg28 (25 : Fin 32), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg28 (26 : Fin 32), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [rg28 (27 : Fin 32), g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4), (0x174, 0x1)] := keep_kk27.trans K28.toL
  clear keep_kk27
  have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K28.w32 (by decide) (by decide)).trans w27_3c
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K28.w32 (by decide) (by decide)).trans w27_44
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K28.w32 (by decide) (by decide)).trans w27_48
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K28.w32 (by decide) (by decide)).trans w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K28.w32 (by decide) (by decide)).trans w27_50
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K28.w32 (by decide) (by decide)).trans w27_64
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K28.w32 (by decide) (by decide)).trans w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K28.w32 (by decide) (by decide)).trans w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K28.w32 (by decide) (by decide)).trans w27_7c
  have w28_170 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = tp := (K28.w32 (by decide) (by decide)).trans w27_170
  have w28_178 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K28.w32 (by decide) (by decide)).trans w27_178
  have w28_17c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := (K28.w32 (by decide) (by decide)).trans w27_17c
  have w28_180 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := (K28.w32 (by decide) (by decide)).trans w27_180
  have w28_184 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := (K28.w32 (by decide) (by decide)).trans w27_184
  have w28_1f0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := (K28.w32 (by decide) (by decide)).trans w27_1f0
  have w28_1f4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg := (K28.w32 (by decide) (by decide)).trans w27_1f4
  have b28_175 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_175
  have b28_176 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> (8 + 8)).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_176
  have b28_177 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> (8 + 16)).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_177
  have b28_190 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := (K28.b8 (by decide) (by decide)).trans b27_190
  have b28_174 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = (tl).extractLsb' 0 8 := by rw [W28, g27_8]
  have q28_191 : ∀ j, j < 47 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_191 j hj)
  have q28_1c0 : ∀ j, j < 48 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_1c0 j hj)
  have q28_1fc : ∀ j, j < 47 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_1fc j hj)
  have q28_22b : ∀ j, j < 48 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_22b j hj)
  have q28_380 : ∀ j, j < 47 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_380 j hj)
  have q28_3af : ∀ j, j < 48 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_3af j hj)
  clear q27_3af q27_380 q27_22b q27_1fc q27_1c0 q27_191 w27_170 b27_190 b27_177 b27_176 b27_175 w27_1f4 w27_1f0 w27_184 w27_180 w27_17c w27_178 w27_7c w27_78 w27_74 w27_64 w27_50 w27_4c w27_48 w27_44 w27_3c g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_11 g27_10 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 rg27 W27 K27 fr27 s27 d27
  have bs28_175 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x175) = ((tl) >>> 8).extractLsb' 0 8 := b28_175
  have bs28_176 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x176) = ((tl) >>> 16).extractLsb' 0 8 := b28_176
  have bs28_177 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x177) = ((tl) >>> 24).extractLsb' 0 8 := b28_177
  have w28_174 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := ld_of_shr_bytes b28_174
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x174 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x175 by sv_addr]; exact bs28_175)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x174 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x176 by sv_addr]; exact bs28_176)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x174 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x177 by sv_addr]; exact bs28_177)
  -- 0x1332: lw
  obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_1332 (off' := 0x1334) (by decide)
    (by rw [g28_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s29 : St n29.mem SV n29 0x1334 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = tl := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
  have g29_11 : reg n29 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_11]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = x27 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
  have g29_10 : reg n29 a0 = w3c := by
    rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g28_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr, w28_3c]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4), (0x174, 0x1)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m29]; exact w28_3c
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m29]; exact w28_44
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m29]; exact w28_48
  have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m29]; exact w28_4c
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m29]; exact w28_50
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m29]; exact w28_64
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m29]; exact w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m29]; exact w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m29]; exact w28_7c
  have w29_170 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = tp := by rw [m29]; exact w28_170
  have w29_174 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m29]; exact w28_174
  have w29_178 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m29]; exact w28_178
  have w29_17c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := by rw [m29]; exact w28_17c
  have w29_180 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := by rw [m29]; exact w28_180
  have w29_184 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := by rw [m29]; exact w28_184
  have w29_1f0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := by rw [m29]; exact w28_1f0
  have w29_1f4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg := by rw [m29]; exact w28_1f4
  have b29_190 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m29]; exact b28_190
  have q29_191 : ∀ j, j < 47 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m29]; exact q28_191 j hj
  have q29_1c0 : ∀ j, j < 48 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m29]; exact q28_1c0 j hj
  have q29_1fc : ∀ j, j < 47 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m29]; exact q28_1fc j hj
  have q29_22b : ∀ j, j < 48 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m29]; exact q28_22b j hj
  have q29_380 : ∀ j, j < 47 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m29]; exact q28_380 j hj
  have q29_3af : ∀ j, j < 48 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m29]; exact q28_3af j hj
  clear q28_3af q28_380 q28_22b q28_1fc q28_1c0 q28_191 b28_174 b28_190 b28_177 b28_176 b28_175 w28_1f4 w28_1f0 w28_184 w28_180 w28_17c w28_178 w28_170 w28_7c w28_78 w28_74 w28_64 w28_50 w28_4c w28_48 w28_44 w28_3c g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_11 g28_10 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 rg28 W28 K28 fr28 s28 d28
  -- 0x1334: sw
  obtain ⟨n30, d30, s30, fr30, K30, W30, rg30⟩ := sv_sw F E29 s29 sv_at_1334 (off' := 0x1336) (c := 0x188)
    (by decide) (by rw [g29_11]; sv_addr) (by decide) (by decide)
  have t30 : Steps n0 n30 := t29.trans d30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keep K30 (by decide)
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rg30 sp, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg30 (3 : Fin 32), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg30 (4 : Fin 32), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = tl := by rw [rg30 (8 : Fin 32), g29_8]
  have g30_10 : reg n30 a0 = w3c := by rw [rg30 a0, g29_10]
  have g30_11 : reg n30 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by rw [rg30 a1, g29_11]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rg30 (18 : Fin 32), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rg30 (19 : Fin 32), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [rg30 (20 : Fin 32), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [rg30 (21 : Fin 32), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [rg30 (22 : Fin 32), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [rg30 (23 : Fin 32), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = x24 := by rw [rg30 (24 : Fin 32), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg30 (25 : Fin 32), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg30 (26 : Fin 32), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = x27 := by rw [rg30 (27 : Fin 32), g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4), (0x174, 0x1), (0x188, 0x4)] := keep_kk29.trans K30.toL
  clear keep_kk29
  have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K30.w32 (by decide) (by decide)).trans w29_3c
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K30.w32 (by decide) (by decide)).trans w29_44
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K30.w32 (by decide) (by decide)).trans w29_48
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K30.w32 (by decide) (by decide)).trans w29_4c
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K30.w32 (by decide) (by decide)).trans w29_50
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K30.w32 (by decide) (by decide)).trans w29_64
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K30.w32 (by decide) (by decide)).trans w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K30.w32 (by decide) (by decide)).trans w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K30.w32 (by decide) (by decide)).trans w29_7c
  have w30_170 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = tp := (K30.w32 (by decide) (by decide)).trans w29_170
  have w30_174 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K30.w32 (by decide) (by decide)).trans w29_174
  have w30_178 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K30.w32 (by decide) (by decide)).trans w29_178
  have w30_17c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := (K30.w32 (by decide) (by decide)).trans w29_17c
  have w30_180 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := (K30.w32 (by decide) (by decide)).trans w29_180
  have w30_184 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := (K30.w32 (by decide) (by decide)).trans w29_184
  have w30_1f0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := (K30.w32 (by decide) (by decide)).trans w29_1f0
  have w30_1f4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg := (K30.w32 (by decide) (by decide)).trans w29_1f4
  have b30_190 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := (K30.b8 (by decide) (by decide)).trans b29_190
  have w30_188 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x188) = w3c := by rw [W30, g29_10]
  have q30_191 : ∀ j, j < 47 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_191 j hj)
  have q30_1c0 : ∀ j, j < 48 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_1c0 j hj)
  have q30_1fc : ∀ j, j < 47 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_1fc j hj)
  have q30_22b : ∀ j, j < 48 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_22b j hj)
  have q30_380 : ∀ j, j < 47 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_380 j hj)
  have q30_3af : ∀ j, j < 48 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_3af j hj)
  clear q29_3af q29_380 q29_22b q29_1fc q29_1c0 q29_191 b29_190 w29_1f4 w29_1f0 w29_184 w29_180 w29_17c w29_178 w29_174 w29_170 w29_7c w29_78 w29_74 w29_64 w29_50 w29_4c w29_48 w29_44 w29_3c g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29 w28_174 bs28_177 bs28_176 bs28_175
  -- 0x1336: lw
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_1336 (off' := 0x1338) (by decide)
    (by rw [g30_2, show B + 0x21A0 + 0x7C = B + 0x21A0 + BitVec.ofNat 32 0x7C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s31 : St n31.mem SV n31 0x1338 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = tl := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
  have g31_11 : reg n31 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_11]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = x24 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = x27 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
  have g31_10 : reg n31 a0 = w7c := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_2, show B + 0x21A0 + 0x7C = B + 0x21A0 + BitVec.ofNat 32 0x7C by sv_addr, w30_7c]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4), (0x174, 0x1), (0x188, 0x4)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m31]; exact w30_3c
  have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m31]; exact w30_44
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m31]; exact w30_48
  have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m31]; exact w30_4c
  have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m31]; exact w30_50
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m31]; exact w30_64
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m31]; exact w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m31]; exact w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m31]; exact w30_7c
  have w31_170 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = tp := by rw [m31]; exact w30_170
  have w31_174 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m31]; exact w30_174
  have w31_178 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m31]; exact w30_178
  have w31_17c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := by rw [m31]; exact w30_17c
  have w31_180 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := by rw [m31]; exact w30_180
  have w31_184 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := by rw [m31]; exact w30_184
  have w31_188 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x188) = w3c := by rw [m31]; exact w30_188
  have w31_1f0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := by rw [m31]; exact w30_1f0
  have w31_1f4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg := by rw [m31]; exact w30_1f4
  have b31_190 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m31]; exact b30_190
  have q31_191 : ∀ j, j < 47 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_191 j hj
  have q31_1c0 : ∀ j, j < 48 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m31]; exact q30_1c0 j hj
  have q31_1fc : ∀ j, j < 47 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_1fc j hj
  have q31_22b : ∀ j, j < 48 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m31]; exact q30_22b j hj
  have q31_380 : ∀ j, j < 47 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_380 j hj
  have q31_3af : ∀ j, j < 48 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m31]; exact q30_3af j hj
  clear q30_3af q30_380 q30_22b q30_1fc q30_1c0 q30_191 w30_188 b30_190 w30_1f4 w30_1f0 w30_184 w30_180 w30_17c w30_178 w30_174 w30_170 w30_7c w30_78 w30_74 w30_64 w30_50 w30_4c w30_48 w30_44 w30_3c g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_11 g30_10 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 rg30 W30 K30 fr30 s30 d30
  -- 0x1338: sw
  obtain ⟨n32, d32, s32, fr32, K32, W32, rg32⟩ := sv_sw F E31 s31 sv_at_1338 (off' := 0x133A) (c := 0x18C)
    (by decide) (by rw [g31_11]; sv_addr) (by decide) (by decide)
  have t32 : Steps n0 n32 := t31.trans d32
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.keep K32 (by decide)
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [rg32 sp, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg32 (3 : Fin 32), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg32 (4 : Fin 32), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = tl := by rw [rg32 (8 : Fin 32), g31_8]
  have g32_10 : reg n32 a0 = w7c := by rw [rg32 a0, g31_10]
  have g32_11 : reg n32 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by rw [rg32 a1, g31_11]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [rg32 (18 : Fin 32), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [rg32 (19 : Fin 32), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [rg32 (20 : Fin 32), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [rg32 (21 : Fin 32), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [rg32 (22 : Fin 32), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [rg32 (23 : Fin 32), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = x24 := by rw [rg32 (24 : Fin 32), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg32 (25 : Fin 32), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg32 (26 : Fin 32), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = x27 := by rw [rg32 (27 : Fin 32), g31_27]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4), (0x174, 0x1), (0x188, 0x4), (0x18C, 0x4)] := keep_kk31.trans K32.toL
  clear keep_kk31
  have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K32.w32 (by decide) (by decide)).trans w31_3c
  have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K32.w32 (by decide) (by decide)).trans w31_44
  have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K32.w32 (by decide) (by decide)).trans w31_48
  have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K32.w32 (by decide) (by decide)).trans w31_4c
  have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K32.w32 (by decide) (by decide)).trans w31_50
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K32.w32 (by decide) (by decide)).trans w31_64
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K32.w32 (by decide) (by decide)).trans w31_74
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K32.w32 (by decide) (by decide)).trans w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K32.w32 (by decide) (by decide)).trans w31_7c
  have w32_170 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = tp := (K32.w32 (by decide) (by decide)).trans w31_170
  have w32_174 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K32.w32 (by decide) (by decide)).trans w31_174
  have w32_178 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K32.w32 (by decide) (by decide)).trans w31_178
  have w32_17c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := (K32.w32 (by decide) (by decide)).trans w31_17c
  have w32_180 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := (K32.w32 (by decide) (by decide)).trans w31_180
  have w32_184 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := (K32.w32 (by decide) (by decide)).trans w31_184
  have w32_188 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x188) = w3c := (K32.w32 (by decide) (by decide)).trans w31_188
  have w32_1f0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := (K32.w32 (by decide) (by decide)).trans w31_1f0
  have w32_1f4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg := (K32.w32 (by decide) (by decide)).trans w31_1f4
  have b32_190 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := (K32.b8 (by decide) (by decide)).trans b31_190
  have w32_18c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x18C) = w7c := by rw [W32, g31_10]
  have q32_191 : ∀ j, j < 47 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K32.range (by decide) (by decide) j hj).trans (q31_191 j hj)
  have q32_1c0 : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K32.range (by decide) (by decide) j hj).trans (q31_1c0 j hj)
  have q32_1fc : ∀ j, j < 47 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K32.range (by decide) (by decide) j hj).trans (q31_1fc j hj)
  have q32_22b : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K32.range (by decide) (by decide) j hj).trans (q31_22b j hj)
  have q32_380 : ∀ j, j < 47 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K32.range (by decide) (by decide) j hj).trans (q31_380 j hj)
  have q32_3af : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K32.range (by decide) (by decide) j hj).trans (q31_3af j hj)
  clear q31_3af q31_380 q31_22b q31_1fc q31_1c0 q31_191 b31_190 w31_1f4 w31_1f0 w31_188 w31_184 w31_180 w31_17c w31_178 w31_174 w31_170 w31_7c w31_78 w31_74 w31_64 w31_50 w31_4c w31_48 w31_44 w31_3c g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_11 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0x133A
  obtain ⟨n33, c33, u33⟩ := s32.block svTsv133a E32.self svTsv133a_end
    ⟨trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem SV n33 0x133E (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock svTsv133a (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
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
  have g33_8 : reg n33 (8 : Fin 32) = tl := by
    rw [rb33, runBlock_reg _ _ _ (8 : Fin 32) s32.zero (by decide), g32_8]
  have g33_11 : reg n33 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by
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
  have g33_25 : reg n33 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = x27 := by
    rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
  have g33_10 : reg n33 a0 = (x21) + BitVec.ofNat 32 0x308 := by
    rw [rb33, ← g32_21]; rfl
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4), (0x174, 0x1), (0x188, 0x4), (0x18C, 0x4)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m33]; exact w32_3c
  have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m33]; exact w32_44
  have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m33]; exact w32_48
  have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m33]; exact w32_4c
  have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m33]; exact w32_50
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m33]; exact w32_64
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m33]; exact w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m33]; exact w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m33]; exact w32_7c
  have w33_170 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = tp := by rw [m33]; exact w32_170
  have w33_174 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m33]; exact w32_174
  have w33_178 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m33]; exact w32_178
  have w33_17c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := by rw [m33]; exact w32_17c
  have w33_180 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := by rw [m33]; exact w32_180
  have w33_184 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := by rw [m33]; exact w32_184
  have w33_188 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x188) = w3c := by rw [m33]; exact w32_188
  have w33_18c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x18C) = w7c := by rw [m33]; exact w32_18c
  have w33_1f0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := by rw [m33]; exact w32_1f0
  have w33_1f4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg := by rw [m33]; exact w32_1f4
  have b33_190 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m33]; exact b32_190
  have q33_191 : ∀ j, j < 47 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m33]; exact q32_191 j hj
  have q33_1c0 : ∀ j, j < 48 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m33]; exact q32_1c0 j hj
  have q33_1fc : ∀ j, j < 47 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m33]; exact q32_1fc j hj
  have q33_22b : ∀ j, j < 48 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m33]; exact q32_22b j hj
  have q33_380 : ∀ j, j < 47 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m33]; exact q32_380 j hj
  have q33_3af : ∀ j, j < 48 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m33]; exact q32_3af j hj
  clear q32_3af q32_380 q32_22b q32_1fc q32_1c0 q32_191 w32_18c b32_190 w32_1f4 w32_1f0 w32_188 w32_184 w32_180 w32_17c w32_178 w32_174 w32_170 w32_7c w32_78 w32_74 w32_64 w32_50 w32_4c w32_48 w32_44 w32_3c g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_10 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 rg32 W32 K32 fr32 s32 d32
  -- 0x133E: sw
  obtain ⟨n34, d34, s34, fr34, K34, W34, rg34⟩ := sv_sw F E33 s33 sv_at_133e (off' := 0x1340) (c := 0x78)
    (by decide) (by rw [g33_2]; sv_addr) (by decide) (by decide)
  have t34 : Steps n0 n34 := t33.trans d34
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.keep K34 (by decide)
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [rg34 sp, g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg34 (3 : Fin 32), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg34 (4 : Fin 32), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = tl := by rw [rg34 (8 : Fin 32), g33_8]
  have g34_10 : reg n34 a0 = (x21) + BitVec.ofNat 32 0x308 := by rw [rg34 a0, g33_10]
  have g34_11 : reg n34 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by rw [rg34 a1, g33_11]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [rg34 (18 : Fin 32), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [rg34 (19 : Fin 32), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = x20 := by rw [rg34 (20 : Fin 32), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [rg34 (21 : Fin 32), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = x22 := by rw [rg34 (22 : Fin 32), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = x23 := by rw [rg34 (23 : Fin 32), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = x24 := by rw [rg34 (24 : Fin 32), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg34 (25 : Fin 32), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg34 (26 : Fin 32), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = x27 := by rw [rg34 (27 : Fin 32), g33_27]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4), (0x174, 0x1), (0x188, 0x4), (0x18C, 0x4), (0x78, 0x4)] := keep_kk33.trans K34.toL
  clear keep_kk33
  have w34_3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K34.w32 (by decide) (by decide)).trans w33_3c
  have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K34.w32 (by decide) (by decide)).trans w33_44
  have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K34.w32 (by decide) (by decide)).trans w33_48
  have w34_4c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K34.w32 (by decide) (by decide)).trans w33_4c
  have w34_50 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K34.w32 (by decide) (by decide)).trans w33_50
  have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K34.w32 (by decide) (by decide)).trans w33_64
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K34.w32 (by decide) (by decide)).trans w33_74
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K34.w32 (by decide) (by decide)).trans w33_7c
  have w34_170 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = tp := (K34.w32 (by decide) (by decide)).trans w33_170
  have w34_174 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K34.w32 (by decide) (by decide)).trans w33_174
  have w34_178 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := (K34.w32 (by decide) (by decide)).trans w33_178
  have w34_17c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := (K34.w32 (by decide) (by decide)).trans w33_17c
  have w34_180 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := (K34.w32 (by decide) (by decide)).trans w33_180
  have w34_184 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := (K34.w32 (by decide) (by decide)).trans w33_184
  have w34_188 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x188) = w3c := (K34.w32 (by decide) (by decide)).trans w33_188
  have w34_18c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x18C) = w7c := (K34.w32 (by decide) (by decide)).trans w33_18c
  have w34_1f0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := (K34.w32 (by decide) (by decide)).trans w33_1f0
  have w34_1f4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg := (K34.w32 (by decide) (by decide)).trans w33_1f4
  have b34_190 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := (K34.b8 (by decide) (by decide)).trans b33_190
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (x21) + BitVec.ofNat 32 0x308 := by rw [W34, g33_10]
  have q34_191 : ∀ j, j < 47 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_191 j hj)
  have q34_1c0 : ∀ j, j < 48 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_1c0 j hj)
  have q34_1fc : ∀ j, j < 47 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_1fc j hj)
  have q34_22b : ∀ j, j < 48 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_22b j hj)
  have q34_380 : ∀ j, j < 47 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_380 j hj)
  have q34_3af : ∀ j, j < 48 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_3af j hj)
  clear q33_3af q33_380 q33_22b q33_1fc q33_1c0 q33_191 b33_190 w33_1f4 w33_1f0 w33_18c w33_188 w33_184 w33_180 w33_17c w33_178 w33_174 w33_170 w33_7c w33_78 w33_74 w33_64 w33_50 w33_4c w33_48 w33_44 w33_3c g33_10 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_11 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
  -- 0x1340
  obtain ⟨n35, c35, u35⟩ := s34.block svTsv1340 E34.self svTsv1340_end
    ⟨trivial, trivial⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have s35 : St n35.mem SV n35 0x1344 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have rb35 : ∀ q, reg n35 q = (runBlock svTsv1340 (n34.mem, reg n34)).2 q := fun q => by rw [u35.regs]
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans c35
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by
    rw [rb35, runBlock_reg _ _ _ sp s34.zero (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (3 : Fin 32) s34.zero (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (4 : Fin 32) s34.zero (by decide), g34_4]
  have g35_10 : reg n35 a0 = (x21) + BitVec.ofNat 32 0x308 := by
    rw [rb35, runBlock_reg _ _ _ a0 s34.zero (by decide), g34_10]
  have g35_11 : reg n35 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by
    rw [rb35, runBlock_reg _ _ _ a1 s34.zero (by decide), g34_11]
  have g35_18 : reg n35 (18 : Fin 32) = out := by
    rw [rb35, runBlock_reg _ _ _ (18 : Fin 32) s34.zero (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by
    rw [rb35, runBlock_reg _ _ _ (19 : Fin 32) s34.zero (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = x20 := by
    rw [rb35, runBlock_reg _ _ _ (20 : Fin 32) s34.zero (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by
    rw [rb35, runBlock_reg _ _ _ (21 : Fin 32) s34.zero (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = x22 := by
    rw [rb35, runBlock_reg _ _ _ (22 : Fin 32) s34.zero (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = x23 := by
    rw [rb35, runBlock_reg _ _ _ (23 : Fin 32) s34.zero (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = x24 := by
    rw [rb35, runBlock_reg _ _ _ (24 : Fin 32) s34.zero (by decide), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb35, runBlock_reg _ _ _ (25 : Fin 32) s34.zero (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb35, runBlock_reg _ _ _ (26 : Fin 32) s34.zero (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = x27 := by
    rw [rb35, runBlock_reg _ _ _ (27 : Fin 32) s34.zero (by decide), g34_27]
  have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 0x100 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, svTsv1340, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_10, g34_11, g34_18, g34_19, g34_20, g34_21, g34_22, g34_23, g34_24, g34_25, g34_26, g34_27, s34.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4), (0x174, 0x1), (0x188, 0x4), (0x18C, 0x4), (0x78, 0x4)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m35]; exact w34_3c
  have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m35]; exact w34_44
  have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m35]; exact w34_48
  have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m35]; exact w34_4c
  have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m35]; exact w34_50
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m35]; exact w34_64
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m35]; exact w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (x21) + BitVec.ofNat 32 0x308 := by rw [m35]; exact w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m35]; exact w34_7c
  have w35_170 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = tp := by rw [m35]; exact w34_170
  have w35_174 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m35]; exact w34_174
  have w35_178 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = w4c := by rw [m35]; exact w34_178
  have w35_17c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = w48 := by rw [m35]; exact w34_17c
  have w35_180 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = w44 := by rw [m35]; exact w34_180
  have w35_184 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = w50 := by rw [m35]; exact w34_184
  have w35_188 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x188) = w3c := by rw [m35]; exact w34_188
  have w35_18c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x18C) = w7c := by rw [m35]; exact w34_18c
  have w35_1f0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = x27 := by rw [m35]; exact w34_1f0
  have w35_1f4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg := by rw [m35]; exact w34_1f4
  have b35_190 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m35]; exact b34_190
  have q35_191 : ∀ j, j < 47 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m35]; exact q34_191 j hj
  have q35_1c0 : ∀ j, j < 48 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1C0 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m35]; exact q34_1c0 j hj
  have q35_1fc : ∀ j, j < 47 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m35]; exact q34_1fc j hj
  have q35_22b : ∀ j, j < 48 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x22B + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m35]; exact q34_22b j hj
  have q35_380 : ∀ j, j < 47 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m35]; exact q34_380 j hj
  have q35_3af : ∀ j, j < 48 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m35]; exact q34_3af j hj
  clear q34_3af q34_380 q34_22b q34_1fc q34_1c0 q34_191 w34_78 b34_190 w34_1f4 w34_1f0 w34_18c w34_188 w34_184 w34_180 w34_17c w34_178 w34_174 w34_170 w34_7c w34_74 w34_64 w34_50 w34_4c w34_48 w34_44 w34_3c g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_11 g34_10 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 rg34 W34 K34 fr34 s34 d34
  exact .inr ⟨n35, t35, s35, E35, V35, fR35, g35_2, g35_3, g35_4, g35_8, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, w35_3c, w35_44, w35_48, w35_4c, w35_50, w35_64, w35_74, w35_78, w35_7c, w35_170, w35_174, w35_178, w35_17c, w35_180, w35_184, w35_188, w35_18c, w35_1f0, w35_1f4, b35_190, q35_191, q35_1c0, q35_1fc, q35_22b, q35_380, q35_3af, keep_kk35.mono (by decide)⟩

end C3.RV32.Sv
