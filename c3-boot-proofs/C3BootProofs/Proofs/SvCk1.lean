import C3BootProofs.Proofs.SvCkpt

/-!
# `sigstore::verify`: the checkpoint's lines

From 0x142E to 0x14C2: the TSA's signature checked, and the checkpoint splits into an origin line, a size line, a root line, a blank line, and a nonempty rest.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCk11558 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x10]
theorem svCk11558_end : blockEnd sigstoreVerifyCode 0x1558 svCk11558 = some 0x155A := by
  simp only [svCk11558]
  rw [blockEnd, sv_at_1558]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk11432 : List BInstr :=
  [.alu .add a0 x0 (19 : Fin 32)]
theorem svCk11432_end : blockEnd sigstoreVerifyCode 0x1432 svCk11432 = some 0x1434 := by
  simp only [svCk11432]
  rw [blockEnd, sv_at_1432]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk11438 : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svCk11438_end : blockEnd sigstoreVerifyCode 0x1438 svCk11438 = some 0x143C := by
  simp only [svCk11438]
  rw [blockEnd, sv_at_1438]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk1143e : List BInstr :=
  [.alu .add a2 x0 (9 : Fin 32)]
theorem svCk1143e_end : blockEnd sigstoreVerifyCode 0x143E svCk1143e = some 0x1440 := by
  simp only [svCk1143e]
  rw [blockEnd, sv_at_143e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk11452 : List BInstr :=
  [.aluImm .add a3 sp 0x400]
theorem svCk11452_end : blockEnd sigstoreVerifyCode 0x1452 svCk11452 = some 0x1456 := by
  simp only [svCk11452]
  rw [blockEnd, sv_at_1452]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk1145e : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svCk1145e_end : blockEnd sigstoreVerifyCode 0x145E svCk1145e = some 0x1462 := by
  simp only [svCk1145e]
  rw [blockEnd, sv_at_145e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk11472 : List BInstr :=
  [.aluImm .add a0 sp 0x400]
theorem svCk11472_end : blockEnd sigstoreVerifyCode 0x1472 svCk11472 = some 0x1476 := by
  simp only [svCk11472]
  rw [blockEnd, sv_at_1472]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk1147c : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svCk1147c_end : blockEnd sigstoreVerifyCode 0x147C svCk1147c = some 0x1480 := by
  simp only [svCk1147c]
  rw [blockEnd, sv_at_147c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk11490 : List BInstr :=
  [.aluImm .add a0 sp 0x400]
theorem svCk11490_end : blockEnd sigstoreVerifyCode 0x1490 svCk11490 = some 0x1494 := by
  simp only [svCk11490]
  rw [blockEnd, sv_at_1490]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk1149c : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svCk1149c_end : blockEnd sigstoreVerifyCode 0x149C svCk1149c = some 0x14A0 := by
  simp only [svCk1149c]
  rw [blockEnd, sv_at_149c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk11878 : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x1A]
theorem svCk11878_end : blockEnd sigstoreVerifyCode 0x1878 svCk11878 = some 0x187A := by
  simp only [svCk11878]
  rw [blockEnd, sv_at_1878]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_ck1 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 pv ckp ckl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x142E (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = pv)
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
    (CK0 : SvCkCode M0)
    (hckp : memLoad32 M0 (bp + 0x18) = ckp)
    (hckl : memLoad32 M0 (bp + 0x1C) = ckl)
    (ckp_in4 : SvIn B (bp + 0x18) 4)
    (ckl_in4 : SvIn B (bp + 0x1C) 4)
    (a_ckp : (bp + 0x18).toNat % 4 = 0)
    (a_ckl : (bp + 0x1C).toNat % 4 = 0)
    (ck_in : SvIn B ckp ckl.toNat) :
    (¬ ((pv ≠ 0) ∧ ∃ ix8, nlScan M0 (ckp) 0 ((ckl).toNat) = some ix8 ∧ ∃ ix18, nlScan M0 ((ckp) + BitVec.ofNat 32 (ix8 + 1)) 0 (((ckl).toNat) - (ix8 + 1)) = some ix18 ∧ ∃ ix26, nlScan M0 (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) 0 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) = some ix26 ∧ ∃ ix34, nlScan M0 ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) 0 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) = some ix34 ∧ (BitVec.ofNat 32 ix34 = 0) ∧ (BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) ≠ 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((pv ≠ 0) ∧
    ∃ ix8, nlScan M0 (ckp) 0 ((ckl).toNat) = some ix8 ∧
    ∃ ix18, nlScan M0 ((ckp) + BitVec.ofNat 32 (ix8 + 1)) 0 (((ckl).toNat) - (ix8 + 1)) = some ix18 ∧
    ∃ ix26, nlScan M0 (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) 0 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) = some ix26 ∧
    ∃ ix34, nlScan M0 ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) 0 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) = some ix34 ∧
    (BitVec.ofNat 32 ix34 = 0) ∧
    (BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) ≠ 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x14C2 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 ix18 ∧
        reg n' (9 : Fin 32) = ckl ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) ∧
        reg n' (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = BitVec.ofNat 32 ix26 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) ∧
        SvKeepL B n0.mem n'.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10), (0x50, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  by_cases hv : pv ≠ 0
  rotate_left
  · -- 0x142E: branch, taken
    obtain ⟨n1, d1, u1⟩ := s0.taken E0.self 0x1558 sv_at_142e
      (by decide) (by rw [g0_10, s0.zero]; exact br_beq_t (Decidable.of_not_not hv))
    have s1 : St n1.mem SV n1 0x1558 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
    have m1 : n1.mem = n0.mem := u1.mem
    have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
    have t1 : Steps n0 n1 := t0.trans (.single d1)
    have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
    have E1 : SvCode n1.mem := E0.fr F fr1
    have V1 : SvSaves B n1.mem v := V0.same m1
    have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, g0_2]
    have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, g0_3]
    have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, g0_4]
    have g1_10 : reg n1 a0 = pv := by rw [u1.regs, g0_10]
    have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, g0_18]
    have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, g0_19]
    have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, g0_20]
    have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, g0_21]
    have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, g0_22]
    have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [u1.regs, g0_23]
    have g1_24 : reg n1 (24 : Fin 32) = x24 := by rw [u1.regs, g0_24]
    have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, g0_25]
    have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, g0_26]
    have g1_27 : reg n1 (27 : Fin 32) = x27 := by rw [u1.regs, g0_27]
    have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
    -- 0x1558
    obtain ⟨n2, c2, u2⟩ := s1.block svCk11558 E1.self svCk11558_end
      ⟨trivial, trivial⟩
    have m2 : n2.mem = n1.mem := u2.mem
    have s2 : St n2.mem SV n2 0x155A (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
    have rb2 : ∀ q, reg n2 q = (runBlock svCk11558 (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
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
    have g2_10 : reg n2 a0 = pv := by
      rw [rb2, runBlock_reg _ _ _ a0 s1.zero (by decide), g1_10]
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
    have g2_8 : reg n2 (8 : Fin 32) = BitVec.ofNat 32 0x10 := by
      rw [rb2]; simp +decide only [runBlock, BInstr.run, svCk11558, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g1_2, g1_3, g1_4, g1_10, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_25, g1_26, g1_27, s1.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
    clear keep_kk1
    clear g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_10 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1
    -- 0x155A: j
    obtain ⟨n3, d3, u3⟩ := s2.jump E2.self sv_at_155a (off' := 0x7A4) (by decide)
      (by rw [s2.pc]; decide)
    have s3 : St n3.mem SV n3 0x7A4 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
    have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x10 := by rw [u3.regs, g2_8]
    have g3_10 : reg n3 a0 = pv := by rw [u3.regs, g2_10]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, g2_20]
    have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, g2_22]
    have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, g2_23]
    have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [u3.regs, g2_24]
    have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [u3.regs, g2_27]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    clear g2_8 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hv h0'), sv_fail F E3 s3 t3 (fun x hx => (fR3 x hx).trans (fM x hx).symm) V3 hret g3_2 g3_18 hO g3_3 g3_4 (by rw [g3_8]; sv_code)⟩
  -- 0x142E: branch, not taken
  obtain ⟨n1, d1, u1⟩ := s0.notTaken E0.self 0x1432 sv_at_142e
    (by decide) (by rw [g0_10, s0.zero]; exact br_beq_f hv)
  have s1 : St n1.mem SV n1 0x1432 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, g0_4]
  have g1_10 : reg n1 a0 = pv := by rw [u1.regs, g0_10]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [u1.regs, g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = x24 := by rw [u1.regs, g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = x27 := by rw [u1.regs, g0_27]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  -- 0x1432
  obtain ⟨n2, c2, u2⟩ := s1.block svCk11432 E1.self svCk11432_end
    ⟨trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem SV n2 0x1434 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock svCk11432 (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
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
  have g2_10 : reg n2 a0 = bp := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svCk11432, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_10, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  clear g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_10 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x1434: lw outside the stack
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_1434 (off' := 0x1436) (by decide)
    (by rw [g2_10]; exact a_ckp)
  have s3 : St n3.mem SV n3 0x1436 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_10 : reg n3 a0 = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_10]
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
  have g3_11 : reg n3 a1 = ckp := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_10, sv_ld fR2 ckp_in4, hckp]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  clear g2_10 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0x1436: lw outside the stack
  obtain ⟨n4, d4, u4⟩ := s3.lw E3.self sv_at_1436 (off' := 0x1438) (by decide)
    (by rw [g3_10]; exact a_ckl)
  have s4 : St n4.mem SV n4 0x1438 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_10 : reg n4 a0 = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_10]
  have g4_11 : reg n4 a1 = ckp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_11]
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
  have g4_9 : reg n4 (9 : Fin 32) = ckl := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_10, sv_ld fR3 ckl_in4, hckl]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  clear g3_11 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x1438
  obtain ⟨n5, c5, u5⟩ := s4.block svCk11438 E4.self svCk11438_end
    ⟨trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x143C (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svCk11438 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_9 : reg n5 (9 : Fin 32) = ckl := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_11 : reg n5 a1 = ckp := by
    rw [rb5, runBlock_reg _ _ _ a1 s4.zero (by decide), g4_11]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svCk11438, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_10, g4_11, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  clear g4_9 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_11 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0x143C: sw
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := sv_sw F E5 s5 sv_at_143c (off' := 0x143E) (c := 0x28)
    (by decide) (by rw [g5_2]; sv_addr) (by decide) (by decide)
  have t6 : Steps n0 n6 := t5.trans d6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rg6 sp, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg6 (3 : Fin 32), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg6 (4 : Fin 32), g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = ckl := by rw [rg6 (9 : Fin 32), g5_9]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [rg6 a0, g5_10]
  have g6_11 : reg n6 a1 = ckp := by rw [rg6 a1, g5_11]
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
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x28, 0x4)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [W6, g5_11]
  clear g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_11 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x143E
  obtain ⟨n7, c7, u7⟩ := s6.block svCk1143e E6.self svCk1143e_end
    ⟨trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x1440 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svCk1143e (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_9 : reg n7 (9 : Fin 32) = ckl := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb7, runBlock_reg _ _ _ a0 s6.zero (by decide), g6_10]
  have g7_11 : reg n7 a1 = ckp := by
    rw [rb7, runBlock_reg _ _ _ a1 s6.zero (by decide), g6_11]
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
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_12 : reg n7 a2 = ckl := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svCk1143e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_9, g6_10, g6_11, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x28, 0x4)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m7]; exact w6_28
  clear w6_28 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_10 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
  -- 0x1440: sv_lineF
  obtain ⟨n8, c8, s8, rk8, K8, L8, fr8⟩ := sv_lineF (oc := 0x420) (nl := (ckl).toNat)
    F E7 (CK0.sv FW fR7) s7 sv_at_1440 sv_at_1444 (by decide) (by decide)
    g7_10 g7_11 (by rw [g7_12, ofNat_toNat_self]) (by decide) (by decide) (.inl ck_in)
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keepL K8 (by decide)
  rw [nlScan_ro FW fR7 (.inl ck_in)] at L8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rk8 sp (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk8 (3 : Fin 32) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk8 (4 : Fin 32) (by decide), g7_4]
  have g8_9 : reg n8 (9 : Fin 32) = ckl := by rw [rk8 (9 : Fin 32) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rk8 (18 : Fin 32) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rk8 (19 : Fin 32) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [rk8 (20 : Fin 32) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [rk8 (21 : Fin 32) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [rk8 (22 : Fin 32) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [rk8 (23 : Fin 32) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [rk8 (24 : Fin 32) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [rk8 (25 : Fin 32) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [rk8 (26 : Fin 32) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by rw [rk8 (27 : Fin 32) (by decide), g7_27]
  obtain ⟨r8, hr8⟩ : ∃ r, nlScan M0 (ckp) 0 ((ckl).toNat) = r := ⟨_, rfl⟩
  rcases r8 with _ | ix8
  · rw [hr8] at L8
    obtain ⟨z0_8, z4_8⟩ := L8
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x28, 0x4), (0x420, 0x10)] := keep_kk7.trans K8
    clear keep_kk7
    have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K8.w32 (by decide) (by decide)).trans w7_28
    have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z0_8
    have b8_424 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := z4_8
    clear w7_28 g7_12 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_11 g7_10 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
    -- 0x1448: lw
    obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_1448 (off' := 0x144C) (by decide)
      (by rw [g8_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s9 : St n9.mem SV n9 0x144C (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
    have g9_9 : reg n9 (9 : Fin 32) = ckl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
    have g9_10 : reg n9 a0 = 0 := by
      rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g8_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w8_420]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x28, 0x4), (0x420, 0x10)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m9]; exact w8_28
    have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m9]; exact w8_420
    have b9_424 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m9]; exact b8_424
    clear b8_424 w8_420 w8_28 z4_8 z0_8
    -- 0x144C: sw
    obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_144c (off' := 0x144E) (c := 0x48)
      (by decide) (by rw [g9_2]; sv_addr) (by decide) (by decide)
    have t10 : Steps n0 n10 := t9.trans d10
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
    have g10_9 : reg n10 (9 : Fin 32) = ckl := by rw [rg10 (9 : Fin 32), g9_9]
    have g10_10 : reg n10 a0 = 0 := by rw [rg10 a0, g9_10]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rg10 (18 : Fin 32), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rg10 (19 : Fin 32), g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [rg10 (20 : Fin 32), g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [rg10 (21 : Fin 32), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [rg10 (22 : Fin 32), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [rg10 (23 : Fin 32), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [rg10 (24 : Fin 32), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [rg10 (25 : Fin 32), g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [rg10 (26 : Fin 32), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [rg10 (27 : Fin 32), g9_27]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4)] := keep_kk9.trans K10.toL
    clear keep_kk9
    have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K10.w32 (by decide) (by decide)).trans w9_28
    have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K10.w32 (by decide) (by decide)).trans w9_420
    have b10_424 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := (K10.b8 (by decide) (by decide)).trans b9_424
    have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = 0 := by rw [W10, g9_10]
    clear b9_424 w9_420 w9_28 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
    -- 0x144E: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x1872 sv_at_144e
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
    have g11_9 : reg n11 (9 : Fin 32) = ckl := by rw [u11.regs, g10_9]
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
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m11]; exact w10_28
    have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = 0 := by rw [m11]; exact w10_48
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m11]; exact w10_420
    have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m11]; exact b10_424
    clear w10_48 b10_424 w10_420 w10_28 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
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
    have g12_9 : reg n12 (9 : Fin 32) = ckl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
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
    have g12_25 : reg n12 (25 : Fin 32) = ((0x1A : BitVec 8)).zeroExtend 32 := by
      rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g11_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b11_424]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m12]; exact w11_28
    have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = 0 := by rw [m12]; exact w11_48
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m12]; exact w11_420
    have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m12]; exact b11_424
    clear b11_424 w11_420 w11_48 w11_28 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
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
    have g13_9 : reg n13 (9 : Fin 32) = ckl := by rw [u13.regs, g12_9]
    have g13_10 : reg n13 a0 = 0 := by rw [u13.regs, g12_10]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = ((0x1A : BitVec 8)).zeroExtend 32 := by rw [u13.regs, g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, g12_27]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m13]; exact w12_28
    have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = 0 := by rw [m13]; exact w12_48
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m13]; exact w12_420
    have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m13]; exact b12_424
    clear b12_424 w12_420 w12_48 w12_28 g12_25 g12_27 g12_26 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    exact .inl ⟨(fun ⟨h0', ix8', h1', _⟩ => by rw [hr8] at h1'; cases h1'), sv_fail_1882 F E13 s13 t13 (fun x hx => (fR13 x hx).trans (fM x hx).symm) V13 hret g13_2 g13_18 hO g13_3 g13_4 (by rw [g13_25]; sv_code)⟩
  have hix8 : ix8 < (ckl).toNat := by have := (nlScan_lt _ _ _ hr8).2; omega
  rw [hr8] at L8
  obtain ⟨y0_8, y4_8, y8_8, y12_8⟩ := L8
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x28, 0x4), (0x420, 0x10)] := keep_kk7.trans K8
  clear keep_kk7
  have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K8.w32 (by decide) (by decide)).trans w7_28
  have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := y0_8
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix8 := y4_8
  have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := y8_8
  have w8_42c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := y12_8
  clear w7_28 g7_12 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_11 g7_10 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x1448: lw
  obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_1448 (off' := 0x144C) (by decide)
    (by rw [g8_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s9 : St n9.mem SV n9 0x144C (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
  have g9_9 : reg n9 (9 : Fin 32) = ckl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
  have g9_10 : reg n9 a0 = ckp := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g8_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w8_420]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x28, 0x4), (0x420, 0x10)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m9]; exact w8_28
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m9]; exact w8_420
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix8 := by rw [m9]; exact w8_424
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m9]; exact w8_428
  have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := by rw [m9]; exact w8_42c
  clear w8_42c w8_428 w8_424 w8_420 w8_28 y12_8 y8_8 y4_8 y0_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 K8 rk8 s8 c8
  -- 0x144C: sw
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_144c (off' := 0x144E) (c := 0x48)
    (by decide) (by rw [g9_2]; sv_addr) (by decide) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_9 : reg n10 (9 : Fin 32) = ckl := by rw [rg10 (9 : Fin 32), g9_9]
  have g10_10 : reg n10 a0 = ckp := by rw [rg10 a0, g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rg10 (18 : Fin 32), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rg10 (19 : Fin 32), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [rg10 (20 : Fin 32), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [rg10 (21 : Fin 32), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [rg10 (22 : Fin 32), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [rg10 (23 : Fin 32), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [rg10 (24 : Fin 32), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [rg10 (25 : Fin 32), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [rg10 (26 : Fin 32), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [rg10 (27 : Fin 32), g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K10.w32 (by decide) (by decide)).trans w9_28
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := (K10.w32 (by decide) (by decide)).trans w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix8 := (K10.w32 (by decide) (by decide)).trans w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := (K10.w32 (by decide) (by decide)).trans w9_428
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := (K10.w32 (by decide) (by decide)).trans w9_42c
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [W10, g9_10]
  clear w9_42c w9_428 w9_424 w9_420 w9_28 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x144E: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0x1452 sv_at_144e
    (by decide) (by rw [g10_10, s10.zero]; exact br_beq_f ck_in.pos_ne)
  have s11 : St n11.mem SV n11 0x1452 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_9 : reg n11 (9 : Fin 32) = ckl := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = ckp := by rw [u11.regs, g10_10]
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
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m11]; exact w10_28
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m11]; exact w10_48
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix8 := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m11]; exact w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := by rw [m11]; exact w10_42c
  clear w10_48 w10_42c w10_428 w10_424 w10_420 w10_28 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0x1452
  obtain ⟨n12, c12, u12⟩ := s11.block svCk11452 E11.self svCk11452_end
    ⟨trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x1456 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svCk11452 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_9 : reg n12 (9 : Fin 32) = ckl := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_10 : reg n12 a0 = ckp := by
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
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svCk11452, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m12]; exact w11_28
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m12]; exact w11_48
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix8 := by rw [m12]; exact w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m12]; exact w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := by rw [m12]; exact w11_42c
  clear w11_42c w11_428 w11_424 w11_420 w11_48 w11_28 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x1456: lw
  obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_1456 (off' := 0x1458) (by decide)
    (by rw [g12_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s13 : St n13.mem SV n13 0x1458 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_9 : reg n13 (9 : Fin 32) = ckl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_9]
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
  have g13_10 : reg n13 a0 = BitVec.ofNat 32 ix8 := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w12_424]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m13]; exact w12_28
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m13]; exact w12_48
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m13]; exact w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix8 := by rw [m13]; exact w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m13]; exact w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := by rw [m13]; exact w12_42c
  clear w12_42c w12_428 w12_424 w12_420 w12_48 w12_28 g12_13 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x1458: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_1458 (off' := 0x145A) (c := 0x44)
    (by decide) (by rw [g13_2]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_9 : reg n14 (9 : Fin 32) = ckl := by rw [rg14 (9 : Fin 32), g13_9]
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 ix8 := by rw [rg14 a0, g13_10]
  have g14_13 : reg n14 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg14 a3, g13_13]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [rg14 (20 : Fin 32), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [rg14 (23 : Fin 32), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K14.w32 (by decide) (by decide)).trans w13_28
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K14.w32 (by decide) (by decide)).trans w13_48
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := (K14.w32 (by decide) (by decide)).trans w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix8 := (K14.w32 (by decide) (by decide)).trans w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := (K14.w32 (by decide) (by decide)).trans w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := (K14.w32 (by decide) (by decide)).trans w13_42c
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [W14, g13_10]
  clear w13_42c w13_428 w13_424 w13_420 w13_48 w13_28 g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_13 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0x145A: lw
  obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_145a (off' := 0x145C) (by decide)
    (by rw [g14_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s15 : St n15.mem SV n15 0x145C (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_9 : reg n15 (9 : Fin 32) = ckl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 ix8 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_10]
  have g15_13 : reg n15 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_13]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_11 : reg n15 a1 = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w14_428]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m15]; exact w14_28
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m15]; exact w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m15]; exact w14_48
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m15]; exact w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix8 := by rw [m15]; exact w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m15]; exact w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := by rw [m15]; exact w14_42c
  clear w14_44 w14_42c w14_428 w14_424 w14_420 w14_48 w14_28 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_13 g14_10 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0x145C: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_145c (off' := 0x145E) (by decide)
    (by rw [g15_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s16 : St n16.mem SV n16 0x145E (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_9 : reg n16 (9 : Fin 32) = ckl := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
  have g16_10 : reg n16 a0 = BitVec.ofNat 32 ix8 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_10]
  have g16_11 : reg n16 a1 = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_11]
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
  have g16_12 : reg n16 a2 = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w15_42c]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m16]; exact w15_28
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m16]; exact w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m16]; exact w15_48
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m16]; exact w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix8 := by rw [m16]; exact w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m16]; exact w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := by rw [m16]; exact w15_42c
  clear w15_42c w15_428 w15_424 w15_420 w15_48 w15_44 w15_28 g15_11 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_13 g15_10 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0x145E
  obtain ⟨n17, c17, u17⟩ := s16.block svCk1145e E16.self svCk1145e_end
    ⟨trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x1462 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svCk1145e (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans c17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by
    rw [rb17, runBlock_reg _ _ _ sp s16.zero (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (3 : Fin 32) s16.zero (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (4 : Fin 32) s16.zero (by decide), g16_4]
  have g17_9 : reg n17 (9 : Fin 32) = ckl := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_11 : reg n17 a1 = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by
    rw [rb17, runBlock_reg _ _ _ a1 s16.zero (by decide), g16_11]
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := by
    rw [rb17, runBlock_reg _ _ _ a2 s16.zero (by decide), g16_12]
  have g17_13 : reg n17 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb17, runBlock_reg _ _ _ a3 s16.zero (by decide), g16_13]
  have g17_18 : reg n17 (18 : Fin 32) = out := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by
    rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by
    rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = x27 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svCk1145e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_9, g16_10, g16_11, g16_12, g16_13, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m17]; exact w16_28
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m17]; exact w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m17]; exact w16_48
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m17]; exact w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix8 := by rw [m17]; exact w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m17]; exact w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix8 + 1) := by rw [m17]; exact w16_42c
  clear w16_42c w16_428 w16_424 w16_420 w16_48 w16_44 w16_28 g16_12 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_13 g16_11 g16_10 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0x1462: sv_lineF
  obtain ⟨n18, c18, s18, rk18, K18, L18, fr18⟩ := sv_lineF (oc := 0x420) (nl := ((ckl).toNat) - (ix8 + 1))
    F E17 (CK0.sv FW fR17) s17 sv_at_1462 sv_at_1466 (by decide) (by decide)
    g17_10 g17_11 (by rw [g17_12, sub_ofNat (Nat.succ_le_of_lt hix8) (by omega)]) (by decide) (by decide) (line_rest (.inl ck_in) hix8)
  have t18 : Steps n0 n18 := t17.trans c18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keepL K18 (by decide)
  rw [nlScan_ro FW fR17 (line_rest (.inl ck_in) hix8)] at L18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [rk18 sp (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk18 (3 : Fin 32) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk18 (4 : Fin 32) (by decide), g17_4]
  have g18_9 : reg n18 (9 : Fin 32) = ckl := by rw [rk18 (9 : Fin 32) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [rk18 (18 : Fin 32) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [rk18 (19 : Fin 32) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [rk18 (20 : Fin 32) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [rk18 (21 : Fin 32) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [rk18 (22 : Fin 32) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [rk18 (23 : Fin 32) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [rk18 (24 : Fin 32) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [rk18 (25 : Fin 32) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [rk18 (26 : Fin 32) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [rk18 (27 : Fin 32) (by decide), g17_27]
  obtain ⟨r18, hr18⟩ : ∃ r, nlScan M0 ((ckp) + BitVec.ofNat 32 (ix8 + 1)) 0 (((ckl).toNat) - (ix8 + 1)) = r := ⟨_, rfl⟩
  rcases r18 with _ | ix18
  · rw [hr18] at L18
    obtain ⟨z0_18, z4_18⟩ := L18
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := keep_kk17.trans K18
    clear keep_kk17
    have w18_28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K18.w32 (by decide) (by decide)).trans w17_28
    have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := (K18.w32 (by decide) (by decide)).trans w17_44
    have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K18.w32 (by decide) (by decide)).trans w17_48
    have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z0_18
    have b18_424 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := z4_18
    clear w17_42c w17_428 w17_424 w17_420 w17_48 w17_44 w17_28 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_13 g17_12 g17_11 g17_9 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
    -- 0x146A: lw
    obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_146a (off' := 0x146E) (by decide)
      (by rw [g18_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s19 : St n19.mem SV n19 0x146E (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
    have g19_9 : reg n19 (9 : Fin 32) = ckl := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
    have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
    have g19_24 : reg n19 (24 : Fin 32) = 0 := by
      rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g18_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w18_420]
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m19]; exact w18_28
    have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m19]; exact w18_44
    have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m19]; exact w18_48
    have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m19]; exact w18_420
    have b19_424 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m19]; exact b18_424
    clear b18_424 w18_420 w18_48 w18_44 w18_28 z4_18 z0_18
    -- 0x146E: branch, taken
    obtain ⟨n20, d20, u20⟩ := s19.taken E19.self 0x1872 sv_at_146e
      (by decide) (by rw [g19_24, s19.zero]; rfl)
    have s20 : St n20.mem SV n20 0x1872 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
    have t20 : Steps n0 n20 := t19.trans (.single d20)
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.same m20
    have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, g19_4]
    have g20_9 : reg n20 (9 : Fin 32) = ckl := by rw [u20.regs, g19_9]
    have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, g19_19]
    have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, g19_20]
    have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [u20.regs, g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = 0 := by rw [u20.regs, g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [u20.regs, g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [u20.regs, g19_27]
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m20]; exact w19_28
    have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m20]; exact w19_44
    have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m20]; exact w19_48
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m20]; exact w19_420
    have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m20]; exact b19_424
    clear b19_424 w19_420 w19_48 w19_44 w19_28 g19_24 g19_27 g19_26 g19_25 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
    -- 0x1872: lbu
    obtain ⟨n21, d21, u21⟩ := s20.lbu E20.self sv_at_1872 (off' := 0x1876) (by decide)
    have s21 : St n21.mem SV n21 0x1876 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
    have g21_9 : reg n21 (9 : Fin 32) = ckl := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = 0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
    have g21_25 : reg n21 (25 : Fin 32) = ((0x1A : BitVec 8)).zeroExtend 32 := by
      rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g20_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b20_424]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m21]; exact w20_28
    have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m21]; exact w20_44
    have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m21]; exact w20_48
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m21]; exact w20_420
    have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m21]; exact b20_424
    clear b20_424 w20_420 w20_48 w20_44 w20_28 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
    -- 0x1876: j
    obtain ⟨n22, d22, u22⟩ := s21.jump E21.self sv_at_1876 (off' := 0x1882) (by decide)
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
    have g22_9 : reg n22 (9 : Fin 32) = ckl := by rw [u22.regs, g21_9]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = 0 := by rw [u22.regs, g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = ((0x1A : BitVec 8)).zeroExtend 32 := by rw [u22.regs, g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m22]; exact w21_28
    have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m22]; exact w21_44
    have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m22]; exact w21_48
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m22]; exact w21_420
    have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m22]; exact b21_424
    clear b21_424 w21_420 w21_48 w21_44 w21_28 g21_25 g21_27 g21_26 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
    exact .inl ⟨(fun ⟨h0', ix8', h1', ix18', h2', _⟩ => by rw [hr8] at h1'; cases h1'; rw [hr18] at h2'; cases h2'), sv_fail_1882 F E22 s22 t22 (fun x hx => (fR22 x hx).trans (fM x hx).symm) V22 hret g22_2 g22_18 hO g22_3 g22_4 (by rw [g22_25]; sv_code)⟩
  have hix18 : ix18 < ((ckl).toNat) - (ix8 + 1) := by have := (nlScan_lt _ _ _ hr18).2; omega
  rw [hr18] at L18
  obtain ⟨y0_18, y4_18, y8_18, y12_18⟩ := L18
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := keep_kk17.trans K18
  clear keep_kk17
  have w18_28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K18.w32 (by decide) (by decide)).trans w17_28
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := (K18.w32 (by decide) (by decide)).trans w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K18.w32 (by decide) (by decide)).trans w17_48
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := y0_18
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix18 := y4_18
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := y8_18
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix8 + 1)) - BitVec.ofNat 32 (ix18 + 1) := y12_18
  clear w17_42c w17_428 w17_424 w17_420 w17_48 w17_44 w17_28 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_13 g17_12 g17_11 g17_9 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x146A: lw
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_146a (off' := 0x146E) (by decide)
    (by rw [g18_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s19 : St n19.mem SV n19 0x146E (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_9 : reg n19 (9 : Fin 32) = ckl := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_24 : reg n19 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w18_420]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m19]; exact w18_28
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m19]; exact w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m19]; exact w18_48
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix18 := by rw [m19]; exact w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m19]; exact w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix8 + 1)) - BitVec.ofNat 32 (ix18 + 1) := by rw [m19]; exact w18_42c
  clear w18_42c w18_428 w18_424 w18_420 w18_48 w18_44 w18_28 y12_18 y8_18 y4_18 y0_18 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 K18 rk18 s18 c18
  -- 0x146E: branch, not taken
  obtain ⟨n20, d20, u20⟩ := s19.notTaken E19.self 0x1472 sv_at_146e
    (by decide) (by rw [g19_24, s19.zero]; exact br_beq_f (line_rest (.inl ck_in) hix8).ne0)
  have s20 : St n20.mem SV n20 0x1472 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, g19_4]
  have g20_9 : reg n20 (9 : Fin 32) = ckl := by rw [u20.regs, g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [u20.regs, g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u20.regs, g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [u20.regs, g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [u20.regs, g19_27]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m20]; exact w19_28
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m20]; exact w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m20]; exact w19_48
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m20]; exact w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix18 := by rw [m20]; exact w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m20]; exact w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix8 + 1)) - BitVec.ofNat 32 (ix18 + 1) := by rw [m20]; exact w19_42c
  clear w19_42c w19_428 w19_424 w19_420 w19_48 w19_44 w19_28 g19_24 g19_27 g19_26 g19_25 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x1472
  obtain ⟨n21, c21, u21⟩ := s20.block svCk11472 E20.self svCk11472_end
    ⟨trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x1476 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svCk11472 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
  have g21_9 : reg n21 (9 : Fin 32) = ckl := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
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
  have g21_24 : reg n21 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_10 : reg n21 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svCk11472, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_9, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m21]; exact w20_28
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m21]; exact w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m21]; exact w20_48
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m21]; exact w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix18 := by rw [m21]; exact w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m21]; exact w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix8 + 1)) - BitVec.ofNat 32 (ix18 + 1) := by rw [m21]; exact w20_42c
  clear w20_42c w20_428 w20_424 w20_420 w20_48 w20_44 w20_28 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
  -- 0x1476: lw
  obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_1476 (off' := 0x1478) (by decide)
    (by rw [g21_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s22 : St n22.mem SV n22 0x1478 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
  have g22_9 : reg n22 (9 : Fin 32) = ckl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
  have g22_10 : reg n22 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_10]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by
    rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g21_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w21_424]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m22]; exact w21_28
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m22]; exact w21_48
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix18 := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix8 + 1)) - BitVec.ofNat 32 (ix18 + 1) := by rw [m22]; exact w21_42c
  clear w21_42c w21_428 w21_424 w21_420 w21_48 w21_44 w21_28 g21_10 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x1478: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_1478 (off' := 0x147A) (by decide)
    (by rw [g22_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s23 : St n23.mem SV n23 0x147A (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = ckl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_10 : reg n23 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_10]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_11 : reg n23 a1 = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w22_428]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m23]; exact w22_28
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m23]; exact w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m23]; exact w22_48
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix18 := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix8 + 1)) - BitVec.ofNat 32 (ix18 + 1) := by rw [m23]; exact w22_42c
  clear w22_42c w22_428 w22_424 w22_420 w22_48 w22_44 w22_28 g22_8 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0x147A: lw
  obtain ⟨n24, d24, u24⟩ := s23.lw E23.self sv_at_147a (off' := 0x147C) (by decide)
    (by rw [g23_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s24 : St n24.mem SV n24 0x147C (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = ckl := by rw [u24.regs, upd_ne (by decide) (by decide), g23_9]
  have g24_10 : reg n24 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_10]
  have g24_11 : reg n24 a1 = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_11]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, upd_ne (by decide) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_27]
  have g24_12 : reg n24 a2 = BitVec.ofNat 32 (((ckl).toNat) - (ix8 + 1)) - BitVec.ofNat 32 (ix18 + 1) := by
    rw [u24.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g23_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w23_42c]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m24]; exact w23_28
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m24]; exact w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m24]; exact w23_48
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix18 := by rw [m24]; exact w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m24]; exact w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix8 + 1)) - BitVec.ofNat 32 (ix18 + 1) := by rw [m24]; exact w23_42c
  clear w23_42c w23_428 w23_424 w23_420 w23_48 w23_44 w23_28 g23_11 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0x147C
  obtain ⟨n25, c25, u25⟩ := s24.block svCk1147c E24.self svCk1147c_end
    ⟨trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0x1480 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svCk1147c (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = ckl := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_11 : reg n25 a1 = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by
    rw [rb25, runBlock_reg _ _ _ a1 s24.zero (by decide), g24_11]
  have g25_12 : reg n25 a2 = BitVec.ofNat 32 (((ckl).toNat) - (ix8 + 1)) - BitVec.ofNat 32 (ix18 + 1) := by
    rw [rb25, runBlock_reg _ _ _ a2 s24.zero (by decide), g24_12]
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
  have g25_24 : reg n25 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by
    rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by
    rw [rb25, runBlock_reg _ _ _ (25 : Fin 32) s24.zero (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = x27 := by
    rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svCk1147c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_10, g24_11, g24_12, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m25]; exact w24_28
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m25]; exact w24_44
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m25]; exact w24_48
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [m25]; exact w24_420
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix18 := by rw [m25]; exact w24_424
  have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m25]; exact w24_428
  have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix8 + 1)) - BitVec.ofNat 32 (ix18 + 1) := by rw [m25]; exact w24_42c
  clear w24_42c w24_428 w24_424 w24_420 w24_48 w24_44 w24_28 g24_12 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_11 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x1480: sv_lineF
  obtain ⟨n26, c26, s26, rk26, K26, L26, fr26⟩ := sv_lineF (oc := 0x420) (nl := (((ckl).toNat) - (ix8 + 1)) - (ix18 + 1))
    F E25 (CK0.sv FW fR25) s25 sv_at_1480 sv_at_1484 (by decide) (by decide)
    g25_10 g25_11 (by rw [g25_12, sub_ofNat (Nat.succ_le_of_lt hix18) (by omega)]) (by decide) (by decide) (line_rest (line_rest (.inl ck_in) hix8) hix18)
  have t26 : Steps n0 n26 := t25.trans c26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keepL K26 (by decide)
  rw [nlScan_ro FW fR25 (line_rest (line_rest (.inl ck_in) hix8) hix18)] at L26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [rk26 sp (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk26 (3 : Fin 32) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk26 (4 : Fin 32) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [rk26 (8 : Fin 32) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = ckl := by rw [rk26 (9 : Fin 32) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [rk26 (18 : Fin 32) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [rk26 (19 : Fin 32) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [rk26 (20 : Fin 32) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [rk26 (21 : Fin 32) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [rk26 (22 : Fin 32) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [rk26 (23 : Fin 32) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [rk26 (24 : Fin 32) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [rk26 (25 : Fin 32) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [rk26 (26 : Fin 32) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [rk26 (27 : Fin 32) (by decide), g25_27]
  obtain ⟨r26, hr26⟩ : ∃ r, nlScan M0 (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) 0 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) = r := ⟨_, rfl⟩
  rcases r26 with _ | ix26
  · rw [hr26] at L26
    obtain ⟨z0_26, z4_26⟩ := L26
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := keep_kk25.trans K26
    clear keep_kk25
    have w26_28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K26.w32 (by decide) (by decide)).trans w25_28
    have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := (K26.w32 (by decide) (by decide)).trans w25_44
    have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K26.w32 (by decide) (by decide)).trans w25_48
    have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z0_26
    have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := z4_26
    clear w25_42c w25_428 w25_424 w25_420 w25_48 w25_44 w25_28 g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_12 g25_11 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
    -- 0x1488: lw
    obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_1488 (off' := 0x148C) (by decide)
      (by rw [g26_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s27 : St n27.mem SV n27 0x148C (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = ckl := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
    have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_20]
    have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
    have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
    have g27_25 : reg n27 (25 : Fin 32) = 0 := by
      rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g26_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w26_420]
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := by rw [m27]; exact keep_kk26
    clear keep_kk26
    have w27_28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m27]; exact w26_28
    have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m27]; exact w26_44
    have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m27]; exact w26_48
    have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m27]; exact w26_420
    have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m27]; exact b26_424
    clear b26_424 w26_420 w26_48 w26_44 w26_28 z4_26 z0_26
    -- 0x148C: branch, taken
    obtain ⟨n28, d28, u28⟩ := s27.taken E27.self 0x1872 sv_at_148c
      (by decide) (by rw [g27_25, s27.zero]; rfl)
    have s28 : St n28.mem SV n28 0x1872 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u28.regs, g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = ckl := by rw [u28.regs, g27_9]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u28.regs, g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = 0 := by rw [u28.regs, g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [u28.regs, g27_27]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m28]; exact w27_28
    have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m28]; exact w27_44
    have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m28]; exact w27_48
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m28]; exact w27_420
    have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m28]; exact b27_424
    clear b27_424 w27_420 w27_48 w27_44 w27_28 g27_25 g27_27 g27_26 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
    -- 0x1872: lbu
    obtain ⟨n29, d29, u29⟩ := s28.lbu E28.self sv_at_1872 (off' := 0x1876) (by decide)
    have s29 : St n29.mem SV n29 0x1876 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = ckl := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
    have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = x27 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
    have g29_25 : reg n29 (25 : Fin 32) = ((0x1A : BitVec 8)).zeroExtend 32 := by
      rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g28_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b28_424]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m29]; exact w28_28
    have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m29]; exact w28_44
    have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m29]; exact w28_48
    have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m29]; exact w28_420
    have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m29]; exact b28_424
    clear b28_424 w28_420 w28_48 w28_44 w28_28 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
    -- 0x1876: j
    obtain ⟨n30, d30, u30⟩ := s29.jump E29.self sv_at_1876 (off' := 0x1882) (by decide)
      (by rw [s29.pc]; decide)
    have s30 : St n30.mem SV n30 0x1882 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u30.regs, g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = ckl := by rw [u30.regs, g29_9]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [u30.regs, g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [u30.regs, g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [u30.regs, g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [u30.regs, g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u30.regs, g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = ((0x1A : BitVec 8)).zeroExtend 32 := by rw [u30.regs, g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [u30.regs, g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = x27 := by rw [u30.regs, g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m30]; exact w29_28
    have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m30]; exact w29_44
    have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m30]; exact w29_48
    have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m30]; exact w29_420
    have b30_424 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m30]; exact b29_424
    clear b29_424 w29_420 w29_48 w29_44 w29_28 g29_25 g29_27 g29_26 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
    exact .inl ⟨(fun ⟨h0', ix8', h1', ix18', h2', ix26', h3', _⟩ => by rw [hr8] at h1'; cases h1'; rw [hr18] at h2'; cases h2'; rw [hr26] at h3'; cases h3'), sv_fail_1882 F E30 s30 t30 (fun x hx => (fR30 x hx).trans (fM x hx).symm) V30 hret g30_2 g30_18 hO g30_3 g30_4 (by rw [g30_25]; sv_code)⟩
  have hix26 : ix26 < (((ckl).toNat) - (ix8 + 1)) - (ix18 + 1) := by have := (nlScan_lt _ _ _ hr26).2; omega
  rw [hr26] at L26
  obtain ⟨y0_26, y4_26, y8_26, y12_26⟩ := L26
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := keep_kk25.trans K26
  clear keep_kk25
  have w26_28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K26.w32 (by decide) (by decide)).trans w25_28
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := (K26.w32 (by decide) (by decide)).trans w25_44
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K26.w32 (by decide) (by decide)).trans w25_48
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := y0_26
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix26 := y4_26
  have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := y8_26
  have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - BitVec.ofNat 32 (ix26 + 1) := y12_26
  clear w25_42c w25_428 w25_424 w25_420 w25_48 w25_44 w25_28 g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_12 g25_11 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0x1488: lw
  obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_1488 (off' := 0x148C) (by decide)
    (by rw [g26_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s27 : St n27.mem SV n27 0x148C (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = ckl := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
  have g27_25 : reg n27 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by
    rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g26_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w26_420]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m27]; exact w26_28
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m27]; exact w26_44
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m27]; exact w26_48
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m27]; exact w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix26 := by rw [m27]; exact w26_424
  have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m27]; exact w26_428
  have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - BitVec.ofNat 32 (ix26 + 1) := by rw [m27]; exact w26_42c
  clear w26_42c w26_428 w26_424 w26_420 w26_48 w26_44 w26_28 y12_26 y8_26 y4_26 y0_26 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 K26 rk26 s26 c26
  -- 0x148C: branch, not taken
  obtain ⟨n28, d28, u28⟩ := s27.notTaken E27.self 0x1490 sv_at_148c
    (by decide) (by rw [g27_25, s27.zero]; exact br_beq_f (line_rest (line_rest (.inl ck_in) hix8) hix18).ne0)
  have s28 : St n28.mem SV n28 0x1490 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u28.regs, g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = ckl := by rw [u28.regs, g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u28.regs, g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u28.regs, g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [u28.regs, g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m28]; exact w27_28
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m28]; exact w27_44
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m28]; exact w27_48
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m28]; exact w27_420
  have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix26 := by rw [m28]; exact w27_424
  have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m28]; exact w27_428
  have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - BitVec.ofNat 32 (ix26 + 1) := by rw [m28]; exact w27_42c
  clear w27_42c w27_428 w27_424 w27_420 w27_48 w27_44 w27_28 g27_25 g27_27 g27_26 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  -- 0x1490
  obtain ⟨n29, c29, u29⟩ := s28.block svCk11490 E28.self svCk11490_end
    ⟨trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem SV n29 0x1494 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock svCk11490 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by
    rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = ckl := by
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
  have g29_24 : reg n29 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by
    rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = x27 := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_10 : reg n29 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svCk11490, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m29]; exact w28_28
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m29]; exact w28_44
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m29]; exact w28_48
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m29]; exact w28_420
  have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix26 := by rw [m29]; exact w28_424
  have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m29]; exact w28_428
  have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - BitVec.ofNat 32 (ix26 + 1) := by rw [m29]; exact w28_42c
  clear w28_42c w28_428 w28_424 w28_420 w28_48 w28_44 w28_28 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  -- 0x1494: lw
  obtain ⟨n30, d30, u30⟩ := s29.lw E29.self sv_at_1494 (off' := 0x1498) (by decide)
    (by rw [g29_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s30 : St n30.mem SV n30 0x1498 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = ckl := by rw [u30.regs, upd_ne (by decide) (by decide), g29_9]
  have g30_10 : reg n30 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, upd_ne (by decide) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by
    rw [u30.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g29_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w29_424]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m30]; exact w29_28
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m30]; exact w29_44
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m30]; exact w29_48
  have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m30]; exact w29_420
  have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix26 := by rw [m30]; exact w29_424
  have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m30]; exact w29_428
  have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - BitVec.ofNat 32 (ix26 + 1) := by rw [m30]; exact w29_42c
  clear w29_42c w29_428 w29_424 w29_420 w29_48 w29_44 w29_28 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
  -- 0x1498: lw
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_1498 (off' := 0x149A) (by decide)
    (by rw [g30_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s31 : St n31.mem SV n31 0x149A (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = ckl := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
  have g31_10 : reg n31 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_10]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
  have g31_11 : reg n31 a1 = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w30_428]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m31]; exact w30_28
  have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m31]; exact w30_44
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m31]; exact w30_48
  have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m31]; exact w30_420
  have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix26 := by rw [m31]; exact w30_424
  have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m31]; exact w30_428
  have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - BitVec.ofNat 32 (ix26 + 1) := by rw [m31]; exact w30_42c
  clear w30_42c w30_428 w30_424 w30_420 w30_48 w30_44 w30_28 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
  -- 0x149A: lw
  obtain ⟨n32, d32, u32⟩ := s31.lw E31.self sv_at_149a (off' := 0x149C) (by decide)
    (by rw [g31_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s32 : St n32.mem SV n32 0x149C (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = ckl := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
  have g32_10 : reg n32 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_10]
  have g32_11 : reg n32 a1 = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_11]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
  have g32_12 : reg n32 a2 = BitVec.ofNat 32 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - BitVec.ofNat 32 (ix26 + 1) := by
    rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g31_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w31_42c]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m32]; exact w31_28
  have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m32]; exact w31_44
  have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m32]; exact w31_48
  have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m32]; exact w31_420
  have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix26 := by rw [m32]; exact w31_424
  have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m32]; exact w31_428
  have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - BitVec.ofNat 32 (ix26 + 1) := by rw [m32]; exact w31_42c
  clear w31_42c w31_428 w31_424 w31_420 w31_48 w31_44 w31_28 g31_11 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0x149C
  obtain ⟨n33, c33, u33⟩ := s32.block svCk1149c E32.self svCk1149c_end
    ⟨trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem SV n33 0x14A0 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock svCk1149c (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
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
  have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by
    rw [rb33, runBlock_reg _ _ _ (8 : Fin 32) s32.zero (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = ckl := by
    rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
  have g33_11 : reg n33 a1 = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by
    rw [rb33, runBlock_reg _ _ _ a1 s32.zero (by decide), g32_11]
  have g33_12 : reg n33 a2 = BitVec.ofNat 32 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - BitVec.ofNat 32 (ix26 + 1) := by
    rw [rb33, runBlock_reg _ _ _ a2 s32.zero (by decide), g32_12]
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
  have g33_24 : reg n33 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by
    rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by
    rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by
    rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by
    rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
  have g33_10 : reg n33 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svCk1149c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_10, g32_11, g32_12, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m33]; exact w32_28
  have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m33]; exact w32_44
  have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m33]; exact w32_48
  have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [m33]; exact w32_420
  have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix26 := by rw [m33]; exact w32_424
  have w33_428 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m33]; exact w32_428
  have w33_42c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - BitVec.ofNat 32 (ix26 + 1) := by rw [m33]; exact w32_42c
  clear w32_42c w32_428 w32_424 w32_420 w32_48 w32_44 w32_28 g32_12 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0x14A0: sv_lineF
  obtain ⟨n34, c34, s34, rk34, K34, L34, fr34⟩ := sv_lineF (oc := 0x420) (nl := ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1))
    F E33 (CK0.sv FW fR33) s33 sv_at_14a0 sv_at_14a4 (by decide) (by decide)
    g33_10 g33_11 (by rw [g33_12, sub_ofNat (Nat.succ_le_of_lt hix26) (by omega)]) (by decide) (by decide) (line_rest (line_rest (line_rest (.inl ck_in) hix8) hix18) hix26)
  have t34 : Steps n0 n34 := t33.trans c34
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.keepL K34 (by decide)
  rw [nlScan_ro FW fR33 (line_rest (line_rest (line_rest (.inl ck_in) hix8) hix18) hix26)] at L34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [rk34 sp (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk34 (3 : Fin 32) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk34 (4 : Fin 32) (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [rk34 (8 : Fin 32) (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = ckl := by rw [rk34 (9 : Fin 32) (by decide), g33_9]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [rk34 (18 : Fin 32) (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [rk34 (19 : Fin 32) (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = x20 := by rw [rk34 (20 : Fin 32) (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [rk34 (21 : Fin 32) (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = x22 := by rw [rk34 (22 : Fin 32) (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = x23 := by rw [rk34 (23 : Fin 32) (by decide), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [rk34 (24 : Fin 32) (by decide), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [rk34 (25 : Fin 32) (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [rk34 (26 : Fin 32) (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [rk34 (27 : Fin 32) (by decide), g33_27]
  obtain ⟨r34, hr34⟩ : ∃ r, nlScan M0 ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) 0 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) = r := ⟨_, rfl⟩
  rcases r34 with _ | ix34
  · rw [hr34] at L34
    obtain ⟨z0_34, z4_34⟩ := L34
    have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := keep_kk33.trans K34
    clear keep_kk33
    have w34_28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K34.w32 (by decide) (by decide)).trans w33_28
    have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := (K34.w32 (by decide) (by decide)).trans w33_44
    have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K34.w32 (by decide) (by decide)).trans w33_48
    have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z0_34
    have b34_424 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := z4_34
    clear w33_42c w33_428 w33_424 w33_420 w33_48 w33_44 w33_28 g33_10 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_12 g33_11 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
    -- 0x14A8: lw
    obtain ⟨n35, d35, u35⟩ := s34.lw E34.self sv_at_14a8 (off' := 0x14AC) (by decide)
      (by rw [g34_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s35 : St n35.mem SV n35 0x14AC (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
    have m35 : n35.mem = n34.mem := u35.mem
    have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
    have t35 : Steps n0 n35 := t34.trans (.single d35)
    have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
    have E35 : SvCode n35.mem := E34.fr F fr35
    have V35 : SvSaves B n35.mem v := V34.same m35
    have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_2]
    have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_3]
    have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_4]
    have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_8]
    have g35_9 : reg n35 (9 : Fin 32) = ckl := by rw [u35.regs, upd_ne (by decide) (by decide), g34_9]
    have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, upd_ne (by decide) (by decide), g34_18]
    have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, upd_ne (by decide) (by decide), g34_19]
    have g35_20 : reg n35 (20 : Fin 32) = x20 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_20]
    have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_21]
    have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_22]
    have g35_23 : reg n35 (23 : Fin 32) = x23 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_23]
    have g35_24 : reg n35 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_24]
    have g35_25 : reg n35 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_25]
    have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_26]
    have g35_27 : reg n35 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_27]
    have g35_10 : reg n35 a0 = 0 := by
      rw [u35.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g34_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w34_420]
    have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m35]; exact keep_kk34
    clear keep_kk34
    have w35_28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m35]; exact w34_28
    have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m35]; exact w34_44
    have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m35]; exact w34_48
    have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m35]; exact w34_420
    have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m35]; exact b34_424
    clear b34_424 w34_420 w34_48 w34_44 w34_28 z4_34 z0_34
    -- 0x14AC: branch, taken
    obtain ⟨n36, d36, u36⟩ := s35.taken E35.self 0x1872 sv_at_14ac
      (by decide) (by rw [g35_10, s35.zero]; rfl)
    have s36 : St n36.mem SV n36 0x1872 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
    have m36 : n36.mem = n35.mem := u36.mem
    have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
    have t36 : Steps n0 n36 := t35.trans (.single d36)
    have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
    have E36 : SvCode n36.mem := E35.fr F fr36
    have V36 : SvSaves B n36.mem v := V35.same m36
    have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, g35_2]
    have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, g35_3]
    have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, g35_4]
    have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u36.regs, g35_8]
    have g36_9 : reg n36 (9 : Fin 32) = ckl := by rw [u36.regs, g35_9]
    have g36_10 : reg n36 a0 = 0 := by rw [u36.regs, g35_10]
    have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, g35_18]
    have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, g35_19]
    have g36_20 : reg n36 (20 : Fin 32) = x20 := by rw [u36.regs, g35_20]
    have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, g35_21]
    have g36_22 : reg n36 (22 : Fin 32) = x22 := by rw [u36.regs, g35_22]
    have g36_23 : reg n36 (23 : Fin 32) = x23 := by rw [u36.regs, g35_23]
    have g36_24 : reg n36 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u36.regs, g35_24]
    have g36_25 : reg n36 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u36.regs, g35_25]
    have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, g35_26]
    have g36_27 : reg n36 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u36.regs, g35_27]
    have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m36]; exact keep_kk35
    clear keep_kk35
    have w36_28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m36]; exact w35_28
    have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m36]; exact w35_44
    have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m36]; exact w35_48
    have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m36]; exact w35_420
    have b36_424 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m36]; exact b35_424
    clear b35_424 w35_420 w35_48 w35_44 w35_28 g35_10 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
    -- 0x1872: lbu
    obtain ⟨n37, d37, u37⟩ := s36.lbu E36.self sv_at_1872 (off' := 0x1876) (by decide)
    have s37 : St n37.mem SV n37 0x1876 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
    have m37 : n37.mem = n36.mem := u37.mem
    have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
    have t37 : Steps n0 n37 := t36.trans (.single d37)
    have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
    have E37 : SvCode n37.mem := E36.fr F fr37
    have V37 : SvSaves B n37.mem v := V36.same m37
    have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_2]
    have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_3]
    have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_4]
    have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_8]
    have g37_9 : reg n37 (9 : Fin 32) = ckl := by rw [u37.regs, upd_ne (by decide) (by decide), g36_9]
    have g37_10 : reg n37 a0 = 0 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_10]
    have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, upd_ne (by decide) (by decide), g36_18]
    have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, upd_ne (by decide) (by decide), g36_19]
    have g37_20 : reg n37 (20 : Fin 32) = x20 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_20]
    have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_21]
    have g37_22 : reg n37 (22 : Fin 32) = x22 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_22]
    have g37_23 : reg n37 (23 : Fin 32) = x23 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_23]
    have g37_24 : reg n37 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_24]
    have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_26]
    have g37_27 : reg n37 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_27]
    have g37_25 : reg n37 (25 : Fin 32) = ((0x1A : BitVec 8)).zeroExtend 32 := by
      rw [u37.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g36_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b36_424]
    have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m37]; exact keep_kk36
    clear keep_kk36
    have w37_28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m37]; exact w36_28
    have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m37]; exact w36_44
    have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m37]; exact w36_48
    have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m37]; exact w36_420
    have b37_424 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m37]; exact b36_424
    clear b36_424 w36_420 w36_48 w36_44 w36_28 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_10 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
    -- 0x1876: j
    obtain ⟨n38, d38, u38⟩ := s37.jump E37.self sv_at_1876 (off' := 0x1882) (by decide)
      (by rw [s37.pc]; decide)
    have s38 : St n38.mem SV n38 0x1882 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
    have m38 : n38.mem = n37.mem := u38.mem
    have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
    have t38 : Steps n0 n38 := t37.trans (.single d38)
    have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
    have E38 : SvCode n38.mem := E37.fr F fr38
    have V38 : SvSaves B n38.mem v := V37.same m38
    have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, g37_2]
    have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, g37_3]
    have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, g37_4]
    have g38_8 : reg n38 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u38.regs, g37_8]
    have g38_9 : reg n38 (9 : Fin 32) = ckl := by rw [u38.regs, g37_9]
    have g38_10 : reg n38 a0 = 0 := by rw [u38.regs, g37_10]
    have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, g37_18]
    have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, g37_19]
    have g38_20 : reg n38 (20 : Fin 32) = x20 := by rw [u38.regs, g37_20]
    have g38_21 : reg n38 (21 : Fin 32) = x21 := by rw [u38.regs, g37_21]
    have g38_22 : reg n38 (22 : Fin 32) = x22 := by rw [u38.regs, g37_22]
    have g38_23 : reg n38 (23 : Fin 32) = x23 := by rw [u38.regs, g37_23]
    have g38_24 : reg n38 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u38.regs, g37_24]
    have g38_25 : reg n38 (25 : Fin 32) = ((0x1A : BitVec 8)).zeroExtend 32 := by rw [u38.regs, g37_25]
    have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [u38.regs, g37_26]
    have g38_27 : reg n38 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u38.regs, g37_27]
    have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m38]; exact keep_kk37
    clear keep_kk37
    have w38_28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m38]; exact w37_28
    have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m38]; exact w37_44
    have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m38]; exact w37_48
    have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m38]; exact w37_420
    have b38_424 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m38]; exact b37_424
    clear b37_424 w37_420 w37_48 w37_44 w37_28 g37_25 g37_27 g37_26 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
    exact .inl ⟨(fun ⟨h0', ix8', h1', ix18', h2', ix26', h3', ix34', h4', _⟩ => by rw [hr8] at h1'; cases h1'; rw [hr18] at h2'; cases h2'; rw [hr26] at h3'; cases h3'; rw [hr34] at h4'; cases h4'), sv_fail_1882 F E38 s38 t38 (fun x hx => (fR38 x hx).trans (fM x hx).symm) V38 hret g38_2 g38_18 hO g38_3 g38_4 (by rw [g38_25]; sv_code)⟩
  have hix34 : ix34 < ((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1) := by have := (nlScan_lt _ _ _ hr34).2; omega
  rw [hr34] at L34
  obtain ⟨y0_34, y4_34, y8_34, y12_34⟩ := L34
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := keep_kk33.trans K34
  clear keep_kk33
  have w34_28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K34.w32 (by decide) (by decide)).trans w33_28
  have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := (K34.w32 (by decide) (by decide)).trans w33_44
  have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K34.w32 (by decide) (by decide)).trans w33_48
  have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := y0_34
  have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := y4_34
  have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := y8_34
  have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := y12_34
  clear w33_42c w33_428 w33_424 w33_420 w33_48 w33_44 w33_28 g33_10 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_12 g33_11 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
  -- 0x14A8: lw
  obtain ⟨n35, d35, u35⟩ := s34.lw E34.self sv_at_14a8 (off' := 0x14AC) (by decide)
    (by rw [g34_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s35 : St n35.mem SV n35 0x14AC (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans (.single d35)
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = ckl := by rw [u35.regs, upd_ne (by decide) (by decide), g34_9]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, upd_ne (by decide) (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, upd_ne (by decide) (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = x20 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = x23 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_27]
  have g35_10 : reg n35 a0 = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by
    rw [u35.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g34_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w34_420]
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m35]; exact w34_28
  have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m35]; exact w34_44
  have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m35]; exact w34_48
  have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m35]; exact w34_420
  have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m35]; exact w34_424
  have w35_428 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m35]; exact w34_428
  have w35_42c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m35]; exact w34_42c
  clear w34_42c w34_428 w34_424 w34_420 w34_48 w34_44 w34_28 y12_34 y8_34 y4_34 y0_34 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 K34 rk34 s34 c34
  -- 0x14AC: branch, not taken
  obtain ⟨n36, d36, u36⟩ := s35.notTaken E35.self 0x14B0 sv_at_14ac
    (by decide) (by rw [g35_10, s35.zero]; exact br_beq_f (line_rest (line_rest (line_rest (.inl ck_in) hix8) hix18) hix26).ne0)
  have s36 : St n36.mem SV n36 0x14B0 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u36.regs, g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = ckl := by rw [u36.regs, g35_9]
  have g36_10 : reg n36 a0 = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [u36.regs, g35_10]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = x20 := by rw [u36.regs, g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = x22 := by rw [u36.regs, g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = x23 := by rw [u36.regs, g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u36.regs, g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u36.regs, g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u36.regs, g35_27]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m36]; exact w35_28
  have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m36]; exact w35_44
  have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m36]; exact w35_48
  have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m36]; exact w35_420
  have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m36]; exact w35_424
  have w36_428 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m36]; exact w35_428
  have w36_42c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m36]; exact w35_42c
  clear w35_42c w35_428 w35_424 w35_420 w35_48 w35_44 w35_28 g35_10 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
  -- 0x14B0: lw
  obtain ⟨n37, d37, u37⟩ := s36.lw E36.self sv_at_14b0 (off' := 0x14B4) (by decide)
    (by rw [g36_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s37 : St n37.mem SV n37 0x14B4 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans (.single d37)
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = ckl := by rw [u37.regs, upd_ne (by decide) (by decide), g36_9]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, upd_ne (by decide) (by decide), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, upd_ne (by decide) (by decide), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = x20 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = x22 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = x23 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_27]
  have g37_10 : reg n37 a0 = BitVec.ofNat 32 ix34 := by
    rw [u37.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g36_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w36_424]
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have w37_28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m37]; exact w36_28
  have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m37]; exact w36_44
  have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m37]; exact w36_48
  have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m37]; exact w36_420
  have w37_424 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m37]; exact w36_424
  have w37_428 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m37]; exact w36_428
  have w37_42c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m37]; exact w36_42c
  clear w36_42c w36_428 w36_424 w36_420 w36_48 w36_44 w36_28 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_10 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
  by_cases hblank : BitVec.ofNat 32 ix34 = 0
  rotate_left
  · -- 0x14B4: branch, taken
    obtain ⟨n38, d38, u38⟩ := s37.taken E37.self 0x1878 sv_at_14b4
      (by decide) (by rw [g37_10, s37.zero]; exact br_bne_t hblank)
    have s38 : St n38.mem SV n38 0x1878 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
    have m38 : n38.mem = n37.mem := u38.mem
    have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
    have t38 : Steps n0 n38 := t37.trans (.single d38)
    have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
    have E38 : SvCode n38.mem := E37.fr F fr38
    have V38 : SvSaves B n38.mem v := V37.same m38
    have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, g37_2]
    have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, g37_3]
    have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, g37_4]
    have g38_8 : reg n38 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u38.regs, g37_8]
    have g38_9 : reg n38 (9 : Fin 32) = ckl := by rw [u38.regs, g37_9]
    have g38_10 : reg n38 a0 = BitVec.ofNat 32 ix34 := by rw [u38.regs, g37_10]
    have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, g37_18]
    have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, g37_19]
    have g38_20 : reg n38 (20 : Fin 32) = x20 := by rw [u38.regs, g37_20]
    have g38_21 : reg n38 (21 : Fin 32) = x21 := by rw [u38.regs, g37_21]
    have g38_22 : reg n38 (22 : Fin 32) = x22 := by rw [u38.regs, g37_22]
    have g38_23 : reg n38 (23 : Fin 32) = x23 := by rw [u38.regs, g37_23]
    have g38_24 : reg n38 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u38.regs, g37_24]
    have g38_25 : reg n38 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u38.regs, g37_25]
    have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [u38.regs, g37_26]
    have g38_27 : reg n38 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u38.regs, g37_27]
    have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m38]; exact keep_kk37
    clear keep_kk37
    have w38_28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m38]; exact w37_28
    have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m38]; exact w37_44
    have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m38]; exact w37_48
    have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m38]; exact w37_420
    have w38_424 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m38]; exact w37_424
    have w38_428 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m38]; exact w37_428
    have w38_42c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m38]; exact w37_42c
    clear w37_42c w37_428 w37_424 w37_420 w37_48 w37_44 w37_28 g37_10 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
    -- 0x1878
    obtain ⟨n39, c39, u39⟩ := s38.block svCk11878 E38.self svCk11878_end
      ⟨trivial, trivial⟩
    have m39 : n39.mem = n38.mem := u39.mem
    have s39 : St n39.mem SV n39 0x187A (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
    have rb39 : ∀ q, reg n39 q = (runBlock svCk11878 (n38.mem, reg n38)).2 q := fun q => by rw [u39.regs]
    have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
    have t39 : Steps n0 n39 := t38.trans c39
    have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
    have E39 : SvCode n39.mem := E38.fr F fr39
    have V39 : SvSaves B n39.mem v := V38.same m39
    have g39_2 : reg n39 sp = B + 0x21A0 := by
      rw [rb39, runBlock_reg _ _ _ sp s38.zero (by decide), g38_2]
    have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb39, runBlock_reg _ _ _ (3 : Fin 32) s38.zero (by decide), g38_3]
    have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb39, runBlock_reg _ _ _ (4 : Fin 32) s38.zero (by decide), g38_4]
    have g39_8 : reg n39 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by
      rw [rb39, runBlock_reg _ _ _ (8 : Fin 32) s38.zero (by decide), g38_8]
    have g39_9 : reg n39 (9 : Fin 32) = ckl := by
      rw [rb39, runBlock_reg _ _ _ (9 : Fin 32) s38.zero (by decide), g38_9]
    have g39_10 : reg n39 a0 = BitVec.ofNat 32 ix34 := by
      rw [rb39, runBlock_reg _ _ _ a0 s38.zero (by decide), g38_10]
    have g39_18 : reg n39 (18 : Fin 32) = out := by
      rw [rb39, runBlock_reg _ _ _ (18 : Fin 32) s38.zero (by decide), g38_18]
    have g39_19 : reg n39 (19 : Fin 32) = bp := by
      rw [rb39, runBlock_reg _ _ _ (19 : Fin 32) s38.zero (by decide), g38_19]
    have g39_20 : reg n39 (20 : Fin 32) = x20 := by
      rw [rb39, runBlock_reg _ _ _ (20 : Fin 32) s38.zero (by decide), g38_20]
    have g39_21 : reg n39 (21 : Fin 32) = x21 := by
      rw [rb39, runBlock_reg _ _ _ (21 : Fin 32) s38.zero (by decide), g38_21]
    have g39_22 : reg n39 (22 : Fin 32) = x22 := by
      rw [rb39, runBlock_reg _ _ _ (22 : Fin 32) s38.zero (by decide), g38_22]
    have g39_23 : reg n39 (23 : Fin 32) = x23 := by
      rw [rb39, runBlock_reg _ _ _ (23 : Fin 32) s38.zero (by decide), g38_23]
    have g39_24 : reg n39 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by
      rw [rb39, runBlock_reg _ _ _ (24 : Fin 32) s38.zero (by decide), g38_24]
    have g39_26 : reg n39 (26 : Fin 32) = x26 := by
      rw [rb39, runBlock_reg _ _ _ (26 : Fin 32) s38.zero (by decide), g38_26]
    have g39_27 : reg n39 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by
      rw [rb39, runBlock_reg _ _ _ (27 : Fin 32) s38.zero (by decide), g38_27]
    have g39_25 : reg n39 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb39]; simp +decide only [runBlock, BInstr.run, svCk11878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g38_2, g38_3, g38_4, g38_8, g38_9, g38_10, g38_18, g38_19, g38_20, g38_21, g38_22, g38_23, g38_24, g38_25, g38_26, g38_27, s38.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m39]; exact keep_kk38
    clear keep_kk38
    have w39_28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m39]; exact w38_28
    have w39_44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m39]; exact w38_44
    have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m39]; exact w38_48
    have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m39]; exact w38_420
    have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m39]; exact w38_424
    have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m39]; exact w38_428
    have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m39]; exact w38_42c
    clear w38_42c w38_428 w38_424 w38_420 w38_48 w38_44 w38_28 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_10 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 m38 s38 u38 d38
    -- 0x187A: j
    obtain ⟨n40, d40, u40⟩ := s39.jump E39.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s39.pc]; decide)
    have s40 : St n40.mem SV n40 0x1882 (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
    have m40 : n40.mem = n39.mem := u40.mem
    have fr40 : ∀ x, SvR B x → n40.mem x = n39.mem x := fun x _ => by rw [m40]
    have t40 : Steps n0 n40 := t39.trans (.single d40)
    have fR40 : ∀ x, SvR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
    have E40 : SvCode n40.mem := E39.fr F fr40
    have V40 : SvSaves B n40.mem v := V39.same m40
    have g40_2 : reg n40 sp = B + 0x21A0 := by rw [u40.regs, g39_2]
    have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u40.regs, g39_3]
    have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u40.regs, g39_4]
    have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u40.regs, g39_8]
    have g40_9 : reg n40 (9 : Fin 32) = ckl := by rw [u40.regs, g39_9]
    have g40_10 : reg n40 a0 = BitVec.ofNat 32 ix34 := by rw [u40.regs, g39_10]
    have g40_18 : reg n40 (18 : Fin 32) = out := by rw [u40.regs, g39_18]
    have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [u40.regs, g39_19]
    have g40_20 : reg n40 (20 : Fin 32) = x20 := by rw [u40.regs, g39_20]
    have g40_21 : reg n40 (21 : Fin 32) = x21 := by rw [u40.regs, g39_21]
    have g40_22 : reg n40 (22 : Fin 32) = x22 := by rw [u40.regs, g39_22]
    have g40_23 : reg n40 (23 : Fin 32) = x23 := by rw [u40.regs, g39_23]
    have g40_24 : reg n40 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u40.regs, g39_24]
    have g40_25 : reg n40 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u40.regs, g39_25]
    have g40_26 : reg n40 (26 : Fin 32) = x26 := by rw [u40.regs, g39_26]
    have g40_27 : reg n40 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u40.regs, g39_27]
    have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m40]; exact keep_kk39
    clear keep_kk39
    have w40_28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m40]; exact w39_28
    have w40_44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m40]; exact w39_44
    have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m40]; exact w39_48
    have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m40]; exact w39_420
    have w40_424 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m40]; exact w39_424
    have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m40]; exact w39_428
    have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m40]; exact w39_42c
    clear w39_42c w39_428 w39_424 w39_420 w39_48 w39_44 w39_28 g39_25 g39_27 g39_26 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_10 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 rb39 s39 m39 u39 c39
    exact .inl ⟨(fun ⟨h0', ix8', h1', ix18', h2', ix26', h3', ix34', h4', h5', _⟩ => by rw [hr8] at h1'; cases h1'; rw [hr18] at h2'; cases h2'; rw [hr26] at h3'; cases h3'; rw [hr34] at h4'; cases h4'; exact hblank h5'), sv_fail_1882 F E40 s40 t40 (fun x hx => (fR40 x hx).trans (fM x hx).symm) V40 hret g40_2 g40_18 hO g40_3 g40_4 (by rw [g40_25]; sv_code)⟩
  -- 0x14B4: branch, not taken
  obtain ⟨n38, d38, u38⟩ := s37.notTaken E37.self 0x14B8 sv_at_14b4
    (by decide) (by rw [g37_10, s37.zero]; exact br_bne_f hblank)
  have s38 : St n38.mem SV n38 0x14B8 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
  have t38 : Steps n0 n38 := t37.trans (.single d38)
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.same m38
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u38.regs, g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = ckl := by rw [u38.regs, g37_9]
  have g38_10 : reg n38 a0 = BitVec.ofNat 32 ix34 := by rw [u38.regs, g37_10]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = x20 := by rw [u38.regs, g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = x21 := by rw [u38.regs, g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = x22 := by rw [u38.regs, g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = x23 := by rw [u38.regs, g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u38.regs, g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u38.regs, g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [u38.regs, g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u38.regs, g37_27]
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m38]; exact keep_kk37
  clear keep_kk37
  have w38_28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m38]; exact w37_28
  have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m38]; exact w37_44
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m38]; exact w37_48
  have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m38]; exact w37_420
  have w38_424 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m38]; exact w37_424
  have w38_428 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m38]; exact w37_428
  have w38_42c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m38]; exact w37_42c
  clear w37_42c w37_428 w37_424 w37_420 w37_48 w37_44 w37_28 g37_10 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
  -- 0x14B8: lw
  obtain ⟨n39, d39, u39⟩ := s38.lw E38.self sv_at_14b8 (off' := 0x14BC) (by decide)
    (by rw [g38_2, show B + 0x21A0 + 0x42C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s39 : St n39.mem SV n39 0x14BC (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
  have t39 : Steps n0 n39 := t38.trans (.single d39)
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.same m39
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u39.regs, upd_ne (by decide) (by decide), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u39.regs, upd_ne (by decide) (by decide), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = ckl := by rw [u39.regs, upd_ne (by decide) (by decide), g38_9]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [u39.regs, upd_ne (by decide) (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = x20 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = x21 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = x22 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = x23 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u39.regs, upd_ne (by decide) (by decide), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u39.regs, upd_ne (by decide) (by decide), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_27]
  have g39_10 : reg n39 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by
    rw [u39.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g38_2, show B + 0x21A0 + 0x42C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w38_42c]
  have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10)] := by rw [m39]; exact keep_kk38
  clear keep_kk38
  have w39_28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m39]; exact w38_28
  have w39_44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m39]; exact w38_44
  have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m39]; exact w38_48
  have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m39]; exact w38_420
  have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m39]; exact w38_424
  have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m39]; exact w38_428
  have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m39]; exact w38_42c
  clear w38_42c w38_428 w38_424 w38_420 w38_48 w38_44 w38_28 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_10 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 m38 s38 u38 d38
  -- 0x14BC: sw
  obtain ⟨n40, d40, s40, fr40, K40, W40, rg40⟩ := sv_sw F E39 s39 sv_at_14bc (off' := 0x14BE) (c := 0x50)
    (by decide) (by rw [g39_2]; sv_addr) (by decide) (by decide)
  have t40 : Steps n0 n40 := t39.trans d40
  have fR40 : ∀ x, SvR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : SvCode n40.mem := E39.fr F fr40
  have V40 : SvSaves B n40.mem v := V39.keep K40 (by decide)
  have g40_2 : reg n40 sp = B + 0x21A0 := by rw [rg40 sp, g39_2]
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg40 (3 : Fin 32), g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg40 (4 : Fin 32), g39_4]
  have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [rg40 (8 : Fin 32), g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = ckl := by rw [rg40 (9 : Fin 32), g39_9]
  have g40_10 : reg n40 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [rg40 a0, g39_10]
  have g40_18 : reg n40 (18 : Fin 32) = out := by rw [rg40 (18 : Fin 32), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [rg40 (19 : Fin 32), g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = x20 := by rw [rg40 (20 : Fin 32), g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = x21 := by rw [rg40 (21 : Fin 32), g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = x22 := by rw [rg40 (22 : Fin 32), g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = x23 := by rw [rg40 (23 : Fin 32), g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [rg40 (24 : Fin 32), g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [rg40 (25 : Fin 32), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = x26 := by rw [rg40 (26 : Fin 32), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [rg40 (27 : Fin 32), g39_27]
  have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10), (0x50, 0x4)] := keep_kk39.trans K40.toL
  clear keep_kk39
  have w40_28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K40.w32 (by decide) (by decide)).trans w39_28
  have w40_44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := (K40.w32 (by decide) (by decide)).trans w39_44
  have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K40.w32 (by decide) (by decide)).trans w39_48
  have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := (K40.w32 (by decide) (by decide)).trans w39_420
  have w40_424 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := (K40.w32 (by decide) (by decide)).trans w39_424
  have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := (K40.w32 (by decide) (by decide)).trans w39_428
  have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := (K40.w32 (by decide) (by decide)).trans w39_42c
  have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [W40, g39_10]
  clear w39_42c w39_428 w39_424 w39_420 w39_48 w39_44 w39_28 g39_10 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 m39 s39 u39 d39
  by_cases hsig : BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) ≠ 0
  rotate_left
  · -- 0x14BE: branch, taken
    obtain ⟨n41, d41, u41⟩ := s40.taken E40.self 0x1878 sv_at_14be
      (by decide) (by rw [g40_10, s40.zero]; exact br_beq_t (Decidable.of_not_not hsig))
    have s41 : St n41.mem SV n41 0x1878 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
    have m41 : n41.mem = n40.mem := u41.mem
    have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
    have t41 : Steps n0 n41 := t40.trans (.single d41)
    have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
    have E41 : SvCode n41.mem := E40.fr F fr41
    have V41 : SvSaves B n41.mem v := V40.same m41
    have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
    have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
    have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
    have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u41.regs, g40_8]
    have g41_9 : reg n41 (9 : Fin 32) = ckl := by rw [u41.regs, g40_9]
    have g41_10 : reg n41 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [u41.regs, g40_10]
    have g41_18 : reg n41 (18 : Fin 32) = out := by rw [u41.regs, g40_18]
    have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [u41.regs, g40_19]
    have g41_20 : reg n41 (20 : Fin 32) = x20 := by rw [u41.regs, g40_20]
    have g41_21 : reg n41 (21 : Fin 32) = x21 := by rw [u41.regs, g40_21]
    have g41_22 : reg n41 (22 : Fin 32) = x22 := by rw [u41.regs, g40_22]
    have g41_23 : reg n41 (23 : Fin 32) = x23 := by rw [u41.regs, g40_23]
    have g41_24 : reg n41 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u41.regs, g40_24]
    have g41_25 : reg n41 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u41.regs, g40_25]
    have g41_26 : reg n41 (26 : Fin 32) = x26 := by rw [u41.regs, g40_26]
    have g41_27 : reg n41 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u41.regs, g40_27]
    have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10), (0x50, 0x4)] := by rw [m41]; exact keep_kk40
    clear keep_kk40
    have w41_28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m41]; exact w40_28
    have w41_44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m41]; exact w40_44
    have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m41]; exact w40_48
    have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m41]; exact w40_50
    have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m41]; exact w40_420
    have w41_424 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m41]; exact w40_424
    have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m41]; exact w40_428
    have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m41]; exact w40_42c
    clear w40_50 w40_42c w40_428 w40_424 w40_420 w40_48 w40_44 w40_28 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_10 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 rg40 W40 K40 fr40 s40 d40
    -- 0x1878
    obtain ⟨n42, c42, u42⟩ := s41.block svCk11878 E41.self svCk11878_end
      ⟨trivial, trivial⟩
    have m42 : n42.mem = n41.mem := u42.mem
    have s42 : St n42.mem SV n42 0x187A (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
    have rb42 : ∀ q, reg n42 q = (runBlock svCk11878 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
    have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
    have t42 : Steps n0 n42 := t41.trans c42
    have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
    have E42 : SvCode n42.mem := E41.fr F fr42
    have V42 : SvSaves B n42.mem v := V41.same m42
    have g42_2 : reg n42 sp = B + 0x21A0 := by
      rw [rb42, runBlock_reg _ _ _ sp s41.zero (by decide), g41_2]
    have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb42, runBlock_reg _ _ _ (3 : Fin 32) s41.zero (by decide), g41_3]
    have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb42, runBlock_reg _ _ _ (4 : Fin 32) s41.zero (by decide), g41_4]
    have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by
      rw [rb42, runBlock_reg _ _ _ (8 : Fin 32) s41.zero (by decide), g41_8]
    have g42_9 : reg n42 (9 : Fin 32) = ckl := by
      rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
    have g42_10 : reg n42 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by
      rw [rb42, runBlock_reg _ _ _ a0 s41.zero (by decide), g41_10]
    have g42_18 : reg n42 (18 : Fin 32) = out := by
      rw [rb42, runBlock_reg _ _ _ (18 : Fin 32) s41.zero (by decide), g41_18]
    have g42_19 : reg n42 (19 : Fin 32) = bp := by
      rw [rb42, runBlock_reg _ _ _ (19 : Fin 32) s41.zero (by decide), g41_19]
    have g42_20 : reg n42 (20 : Fin 32) = x20 := by
      rw [rb42, runBlock_reg _ _ _ (20 : Fin 32) s41.zero (by decide), g41_20]
    have g42_21 : reg n42 (21 : Fin 32) = x21 := by
      rw [rb42, runBlock_reg _ _ _ (21 : Fin 32) s41.zero (by decide), g41_21]
    have g42_22 : reg n42 (22 : Fin 32) = x22 := by
      rw [rb42, runBlock_reg _ _ _ (22 : Fin 32) s41.zero (by decide), g41_22]
    have g42_23 : reg n42 (23 : Fin 32) = x23 := by
      rw [rb42, runBlock_reg _ _ _ (23 : Fin 32) s41.zero (by decide), g41_23]
    have g42_24 : reg n42 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by
      rw [rb42, runBlock_reg _ _ _ (24 : Fin 32) s41.zero (by decide), g41_24]
    have g42_26 : reg n42 (26 : Fin 32) = x26 := by
      rw [rb42, runBlock_reg _ _ _ (26 : Fin 32) s41.zero (by decide), g41_26]
    have g42_27 : reg n42 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by
      rw [rb42, runBlock_reg _ _ _ (27 : Fin 32) s41.zero (by decide), g41_27]
    have g42_25 : reg n42 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb42]; simp +decide only [runBlock, BInstr.run, svCk11878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10), (0x50, 0x4)] := by rw [m42]; exact keep_kk41
    clear keep_kk41
    have w42_28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m42]; exact w41_28
    have w42_44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m42]; exact w41_44
    have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m42]; exact w41_48
    have w42_50 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m42]; exact w41_50
    have w42_420 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m42]; exact w41_420
    have w42_424 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m42]; exact w41_424
    have w42_428 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m42]; exact w41_428
    have w42_42c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m42]; exact w41_42c
    clear w41_42c w41_428 w41_424 w41_420 w41_50 w41_48 w41_44 w41_28 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
    -- 0x187A: j
    obtain ⟨n43, d43, u43⟩ := s42.jump E42.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s42.pc]; decide)
    have s43 : St n43.mem SV n43 0x1882 (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
    have m43 : n43.mem = n42.mem := u43.mem
    have fr43 : ∀ x, SvR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
    have t43 : Steps n0 n43 := t42.trans (.single d43)
    have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
    have E43 : SvCode n43.mem := E42.fr F fr43
    have V43 : SvSaves B n43.mem v := V42.same m43
    have g43_2 : reg n43 sp = B + 0x21A0 := by rw [u43.regs, g42_2]
    have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u43.regs, g42_3]
    have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u43.regs, g42_4]
    have g43_8 : reg n43 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u43.regs, g42_8]
    have g43_9 : reg n43 (9 : Fin 32) = ckl := by rw [u43.regs, g42_9]
    have g43_10 : reg n43 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [u43.regs, g42_10]
    have g43_18 : reg n43 (18 : Fin 32) = out := by rw [u43.regs, g42_18]
    have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [u43.regs, g42_19]
    have g43_20 : reg n43 (20 : Fin 32) = x20 := by rw [u43.regs, g42_20]
    have g43_21 : reg n43 (21 : Fin 32) = x21 := by rw [u43.regs, g42_21]
    have g43_22 : reg n43 (22 : Fin 32) = x22 := by rw [u43.regs, g42_22]
    have g43_23 : reg n43 (23 : Fin 32) = x23 := by rw [u43.regs, g42_23]
    have g43_24 : reg n43 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u43.regs, g42_24]
    have g43_25 : reg n43 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u43.regs, g42_25]
    have g43_26 : reg n43 (26 : Fin 32) = x26 := by rw [u43.regs, g42_26]
    have g43_27 : reg n43 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u43.regs, g42_27]
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10), (0x50, 0x4)] := by rw [m43]; exact keep_kk42
    clear keep_kk42
    have w43_28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m43]; exact w42_28
    have w43_44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m43]; exact w42_44
    have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m43]; exact w42_48
    have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m43]; exact w42_50
    have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m43]; exact w42_420
    have w43_424 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m43]; exact w42_424
    have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m43]; exact w42_428
    have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m43]; exact w42_42c
    clear w42_42c w42_428 w42_424 w42_420 w42_50 w42_48 w42_44 w42_28 g42_25 g42_27 g42_26 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_10 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    exact .inl ⟨(fun ⟨h0', ix8', h1', ix18', h2', ix26', h3', ix34', h4', h5', h6', _⟩ => by rw [hr8] at h1'; cases h1'; rw [hr18] at h2'; cases h2'; rw [hr26] at h3'; cases h3'; rw [hr34] at h4'; cases h4'; exact hsig h6'), sv_fail_1882 F E43 s43 t43 (fun x hx => (fR43 x hx).trans (fM x hx).symm) V43 hret g43_2 g43_18 hO g43_3 g43_4 (by rw [g43_25]; sv_code)⟩
  -- 0x14BE: branch, not taken
  obtain ⟨n41, d41, u41⟩ := s40.notTaken E40.self 0x14C2 sv_at_14be
    (by decide) (by rw [g40_10, s40.zero]; exact br_beq_f hsig)
  have s41 : St n41.mem SV n41 0x14C2 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
  have m41 : n41.mem = n40.mem := u41.mem
  have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
  have t41 : Steps n0 n41 := t40.trans (.single d41)
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.same m41
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 ix18 := by rw [u41.regs, g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = ckl := by rw [u41.regs, g40_9]
  have g41_10 : reg n41 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [u41.regs, g40_10]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [u41.regs, g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [u41.regs, g40_19]
  have g41_20 : reg n41 (20 : Fin 32) = x20 := by rw [u41.regs, g40_20]
  have g41_21 : reg n41 (21 : Fin 32) = x21 := by rw [u41.regs, g40_21]
  have g41_22 : reg n41 (22 : Fin 32) = x22 := by rw [u41.regs, g40_22]
  have g41_23 : reg n41 (23 : Fin 32) = x23 := by rw [u41.regs, g40_23]
  have g41_24 : reg n41 (24 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix8 + 1) := by rw [u41.regs, g40_24]
  have g41_25 : reg n41 (25 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1) := by rw [u41.regs, g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = x26 := by rw [u41.regs, g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = BitVec.ofNat 32 ix26 := by rw [u41.regs, g40_27]
  have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10), (0x50, 0x4)] := by rw [m41]; exact keep_kk40
  clear keep_kk40
  have w41_28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m41]; exact w40_28
  have w41_44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8 := by rw [m41]; exact w40_44
  have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m41]; exact w40_48
  have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m41]; exact w40_50
  have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1) := by rw [m41]; exact w40_420
  have w41_424 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix34 := by rw [m41]; exact w40_424
  have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix8 + 1)) + BitVec.ofNat 32 (ix18 + 1)) + BitVec.ofNat 32 (ix26 + 1)) + BitVec.ofNat 32 (ix34 + 1) := by rw [m41]; exact w40_428
  have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8 + 1)) - (ix18 + 1)) - (ix26 + 1)) - BitVec.ofNat 32 (ix34 + 1) := by rw [m41]; exact w40_42c
  clear w40_50 w40_42c w40_428 w40_424 w40_420 w40_48 w40_44 w40_28 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_10 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 rg40 W40 K40 fr40 s40 d40
  exact .inr ⟨hv, ix8, hr8, ix18, hr18, ix26, hr26, ix34, hr34, hblank, hsig, n41, t41, s41, E41, V41, fR41, g41_2, g41_3, g41_4, g41_8, g41_9, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, w41_28, w41_44, w41_48, w41_50, w41_428, w41_42c, keep_kk41.mono (by decide)⟩

end C3.RV32.Sv
