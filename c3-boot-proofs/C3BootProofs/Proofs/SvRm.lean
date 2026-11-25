import C3BootProofs.Proofs.SvRk

/-!
# `sigstore::verify`: the inclusion proof

From 0x1974 to 0x19D0: `root_from_inclusion` rebuilds a root from the leaf hash at offset 0x400, the entry's index, the checkpoint's size, and the bundle's proof, and the root is the checkpoint's.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svRm197c : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a5 sp 0x400, .alu .add a1 x0 (21 : Fin 32), .alu .add a2 x0 (24 : Fin 32)]
theorem svRm197c_end : blockEnd sigstoreVerifyCode 0x197C svRm197c = some 0x1988 := by
  simp only [svRm197c]
  rw [blockEnd, sv_at_197c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1980]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1984]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1986]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRm199e : List BInstr :=
  [.alu .add (20 : Fin 32) x0 (9 : Fin 32)]
theorem svRm199e_end : blockEnd sigstoreVerifyCode 0x199E svRm199e = some 0x19A0 := by
  simp only [svRm199e]
  rw [blockEnd, sv_at_199e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRm19aa : List BInstr :=
  [.aluImm .add (8 : Fin 32) sp 0x3A8, .aluImm .add a1 sp 0x422, .aluImm .add a0 sp 0x1FD, .aluImm .add a2 x0 0x1F]
theorem svRm19aa_end : blockEnd sigstoreVerifyCode 0x19AA svRm19aa = some 0x19B6 := by
  simp only [svRm19aa]
  rw [blockEnd, sv_at_19aa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_19ac]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_19b0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_19b4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRm19c2 : List BInstr :=
  [.aluImm .add a0 sp 0x1FC, .alu .add a1 x0 (8 : Fin 32)]
theorem svRm19c2_end : blockEnd sigstoreVerifyCode 0x19C2 svRm19c2 = some 0x19C6 := by
  simp only [svRm19c2]
  rw [blockEnd, sv_at_19c2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_19c4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_rm {B out bp x20 x21 x22 x23 x24 x25 x26 x27 w64 w74 pp pl : Word} {rt lh : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x1974 (reg n0))
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
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (S2 : SvSha2Code M0)
    (RS : SvRoSep B)
    (RK0 : SvRkCode M0)
    (b0_3a8 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8)
    (q0_3a9 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))
    (D0 : memBytes n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 32 = lh)
    (hpp : memLoad32 M0 (bp + 0x10) = pp)
    (hpl : memLoad32 M0 (bp + 0x14) = pl)
    (pp_in4 : SvIn B (bp + 0x10) 4)
    (pl_in4 : SvIn B (bp + 0x14) 4)
    (a_pp : (bp + 0x10).toNat % 4 = 0)
    (a_pl : (bp + 0x14).toNat % 4 = 0)
    (pp_in : SvIn B pp pl.toNat) :
    (¬ (∃ root6, rootFromInclusion (pair64 (x21) (x24)) (pair64 (w64) (w74)) (lh) (memBytes M0 (pp) ((pl).toNat)) = some root6 ∧ (b32 root6 = b32 rt) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ root6, rootFromInclusion (pair64 (x21) (x24)) (pair64 (w64) (w74)) (lh) (memBytes M0 (pp) ((pl).toNat)) = some root6 ∧
    (b32 root6 = b32 rt) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x19D0 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x3A8 ∧
        reg n' (9 : Fin 32) = (BitVec.ofNat 8 (root6.getD 0 0)).zeroExtend 32 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1FC) = BitVec.ofNat 8 (root6.getD 0 0) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6.getD 0 0) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FD + j)) = BitVec.ofNat 8 (root6.getD (1 + j) 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x21), (0x1FD, 0x1F), (0x1FC, 0x1)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x1974: lw outside the stack
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_1974 (off' := 0x1978) (by decide)
    (by rw [g0_19]; exact a_pp)
  have s1 : St n1.mem SV n1 0x1978 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
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
  have g1_16 : reg n1 a6 = pp := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_19, sv_ld fR0 pp_in4, hpp]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m1]; exact w0_64
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m1]; exact w0_74
  have b1_3a8 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m1]; exact b0_3a8
  have q1_3a9 : ∀ j, j < 31 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m1]; exact q0_3a9 j hj
  have D1 : memBytes n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 32 = lh := by rw [m1]; exact D0
  -- 0x1978: lw outside the stack
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_1978 (off' := 0x197C) (by decide)
    (by rw [g1_19]; exact a_pl)
  have s2 : St n2.mem SV n2 0x197C (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_16 : reg n2 a6 = pp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_16]
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
  have g2_17 : reg n2 a7 = pl := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_19, sv_ld fR1 pl_in4, hpl]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m2]; exact w1_64
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m2]; exact w1_74
  have b2_3a8 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m2]; exact b1_3a8
  have q2_3a9 : ∀ j, j < 31 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m2]; exact q1_3a9 j hj
  clear q1_3a9 b1_3a8 w1_74 w1_64 g1_16 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  have D2 : memBytes n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 32 = lh := by rw [m2]; exact D1
  -- 0x197C
  obtain ⟨n3, c3, u3⟩ := s2.block svRm197c E2.self svRm197c_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0x1988 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock svRm197c (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
  have g3_16 : reg n3 a6 = pp := by
    rw [rb3, runBlock_reg _ _ _ a6 s2.zero (by decide), g2_16]
  have g3_17 : reg n3 a7 = pl := by
    rw [rb3, runBlock_reg _ _ _ a7 s2.zero (by decide), g2_17]
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
  have g3_24 : reg n3 (24 : Fin 32) = x24 := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by
    rw [rb3, runBlock_reg _ _ _ (25 : Fin 32) s2.zero (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = x27 := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svRm197c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_16, g2_17, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_11 : reg n3 a1 = x21 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svRm197c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_16, g2_17, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_12 : reg n3 a2 = x24 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svRm197c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_16, g2_17, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_15 : reg n3 a5 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svRm197c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_16, g2_17, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m3]; exact w2_64
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m3]; exact w2_74
  have b3_3a8 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m3]; exact b2_3a8
  have q3_3a9 : ∀ j, j < 31 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m3]; exact q2_3a9 j hj
  clear q2_3a9 b2_3a8 w2_74 w2_64 g2_17 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_16 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  have D3 : memBytes n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 32 = lh := by rw [m3]; exact D2
  -- 0x1988: lw
  obtain ⟨n4, d4, u4⟩ := s3.lw E3.self sv_at_1988 (off' := 0x198A) (by decide)
    (by rw [g3_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s4 : St n4.mem SV n4 0x198A (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_10]
  have g4_11 : reg n4 a1 = x21 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_11]
  have g4_12 : reg n4 a2 = x24 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_12]
  have g4_15 : reg n4 a5 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_15]
  have g4_16 : reg n4 a6 = pp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_16]
  have g4_17 : reg n4 a7 = pl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_17]
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
  have g4_13 : reg n4 a3 = w64 := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr, w3_64]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m4]; exact w3_64
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m4]; exact w3_74
  have b4_3a8 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m4]; exact b3_3a8
  have q4_3a9 : ∀ j, j < 31 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m4]; exact q3_3a9 j hj
  clear q3_3a9 b3_3a8 w3_74 w3_64 g3_15 g3_12 g3_11 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_17 g3_16 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  have D4 : memBytes n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 32 = lh := by rw [m4]; exact D3
  -- 0x198A: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_198a (off' := 0x198C) (by decide)
    (by rw [g4_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0x198C (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
  have g5_11 : reg n5 a1 = x21 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_11]
  have g5_12 : reg n5 a2 = x24 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_12]
  have g5_13 : reg n5 a3 = w64 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_13]
  have g5_15 : reg n5 a5 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_15]
  have g5_16 : reg n5 a6 = pp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_16]
  have g5_17 : reg n5 a7 = pl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_17]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
  have g5_14 : reg n5 a4 = w74 := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr, w4_74]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m5]; exact w4_64
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m5]; exact w4_74
  have b5_3a8 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m5]; exact b4_3a8
  have q5_3a9 : ∀ j, j < 31 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_3a9 j hj
  clear q4_3a9 b4_3a8 w4_74 w4_64 g4_13 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_17 g4_16 g4_15 g4_12 g4_11 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  have D5 : memBytes n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 32 = lh := by rw [m5]; exact D4
  -- 0x198C: sv_rfiF
  obtain ⟨n6, c6, s6, sp6, rk6, K6, R6, fr6⟩ := sv_rfiF (oc := 0x420) (lc := 0x400) (np := (pl).toNat)
    F E5 (S2.sv FW RS fR5) (RK0.sv FW fR5) RS s5 sv_at_198c sv_at_1990 (by decide) (by decide) g5_2
    g5_10 g5_15 g5_16 (by rw [g5_17, ofNat_toNat_self]) (by decide) (by decide) (Or.inl pp_in)
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keepL K6 (by decide)
  rw [g5_11, g5_12, g5_13, g5_14, D5, sv_mbRo2 RS fR5 (Or.inl pp_in)] at R6
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk6 (3 : Fin 32) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk6 (4 : Fin 32) (by decide), g5_4]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [rk6 (18 : Fin 32) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [rk6 (19 : Fin 32) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [rk6 (20 : Fin 32) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [rk6 (21 : Fin 32) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [rk6 (22 : Fin 32) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [rk6 (23 : Fin 32) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [rk6 (24 : Fin 32) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [rk6 (25 : Fin 32) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [rk6 (26 : Fin 32) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by rw [rk6 (27 : Fin 32) (by decide), g5_27]
  have g6_2 : reg n6 sp = B + 0x21A0 := sp6
  obtain ⟨r6, hr6⟩ : ∃ r, rootFromInclusion (pair64 (x21) (x24)) (pair64 (w64) (w74)) (lh) (memBytes M0 (pp) ((pl).toNat)) = r := ⟨_, rfl⟩
  rw [hr6] at R6
  rcases r6 with _ | root6
  · obtain ⟨z6, y6⟩ := R6
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x21)] := keep_kk5.trans K6
    clear keep_kk5
    have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K6.w32 (by decide) (by decide)).trans w5_64
    have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K6.w32 (by decide) (by decide)).trans w5_74
    have b6_3a8 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := (K6.b8 (by decide) (by decide)).trans b5_3a8
    have q6_3a9 : ∀ j, j < 31 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K6.range (by decide) (by decide) j hj).trans (q5_3a9 j hj)
    have b6_420 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := z6
    have b6_421 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = (0x1B : BitVec 8) := y6
    clear q5_3a9 b5_3a8 w5_74 w5_64 g5_14 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_17 g5_16 g5_15 g5_13 g5_12 g5_11 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    -- 0x1994: lbu
    obtain ⟨n7, d7, u7⟩ := s6.lbu E6.self sv_at_1994 (off' := 0x1998) (by decide)
    have s7 : St n7.mem SV n7 0x1998 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
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
    have g7_10 : reg n7 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g6_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b6_420]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x21)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
    have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m7]; exact w6_74
    have b7_3a8 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m7]; exact b6_3a8
    have b7_420 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m7]; exact b6_420
    have b7_421 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = (0x1B : BitVec 8) := by rw [m7]; exact b6_421
    have q7_3a9 : ∀ j, j < 31 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m7]; exact q6_3a9 j hj
    clear b6_421 b6_420 q6_3a9 b6_3a8 w6_74 w6_64 y6 z6
    -- 0x1998: lbu
    obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_1998 (off' := 0x199C) (by decide)
    have s8 : St n8.mem SV n8 0x199C (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
    have g8_10 : reg n8 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_10]
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
    have g8_9 : reg n8 (9 : Fin 32) = ((0x1B : BitVec 8)).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g7_2, show B + 0x21A0 + 0x421 = B + 0x21A0 + BitVec.ofNat 32 0x421 by sv_addr, b7_421]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x21)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
    have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
    have b8_3a8 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m8]; exact b7_3a8
    have b8_420 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m8]; exact b7_420
    have b8_421 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = (0x1B : BitVec 8) := by rw [m8]; exact b7_421
    have q8_3a9 : ∀ j, j < 31 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m8]; exact q7_3a9 j hj
    clear q7_3a9 b7_421 b7_420 b7_3a8 w7_74 w7_64 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
    -- 0x199C: branch, not taken
    obtain ⟨n9, d9, u9⟩ := s8.notTaken E8.self 0x199E sv_at_199c
      (by decide) (by rw [g8_10, s8.zero]; decide)
    have s9 : St n9.mem SV n9 0x199E (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
    have g9_9 : reg n9 (9 : Fin 32) = ((0x1B : BitVec 8)).zeroExtend 32 := by rw [u9.regs, g8_9]
    have g9_10 : reg n9 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u9.regs, g8_10]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [u9.regs, g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [u9.regs, g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x21)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
    have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m9]; exact w8_74
    have b9_3a8 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m9]; exact b8_3a8
    have b9_420 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m9]; exact b8_420
    have b9_421 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = (0x1B : BitVec 8) := by rw [m9]; exact b8_421
    have q9_3a9 : ∀ j, j < 31 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m9]; exact q8_3a9 j hj
    clear q8_3a9 b8_421 b8_420 b8_3a8 w8_74 w8_64 g8_9 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    -- 0x199E
    obtain ⟨n10, c10, u10⟩ := s9.block svRm199e E9.self svRm199e_end
      ⟨trivial, trivial⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have s10 : St n10.mem SV n10 0x19A0 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have rb10 : ∀ q, reg n10 q = (runBlock svRm199e (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
    have g10_9 : reg n10 (9 : Fin 32) = ((0x1B : BitVec 8)).zeroExtend 32 := by
      rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
    have g10_10 : reg n10 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [rb10, runBlock_reg _ _ _ a0 s9.zero (by decide), g9_10]
    have g10_18 : reg n10 (18 : Fin 32) = out := by
      rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by
      rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
    have g10_21 : reg n10 (21 : Fin 32) = x21 := by
      rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = x22 := by
      rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = x23 := by
      rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = x24 := by
      rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = x25 := by
      rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = x26 := by
      rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = x27 := by
      rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
    have g10_20 : reg n10 (20 : Fin 32) = ((0x1B : BitVec 8)).zeroExtend 32 := by
      rw [rb10]; simp +decide only [runBlock, BInstr.run, svRm199e, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g9_2, g9_3, g9_4, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x21)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
    have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
    have b10_3a8 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m10]; exact b9_3a8
    have b10_420 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m10]; exact b9_420
    have b10_421 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = (0x1B : BitVec 8) := by rw [m10]; exact b9_421
    have q10_3a9 : ∀ j, j < 31 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_3a9 j hj
    clear q9_3a9 b9_421 b9_420 b9_3a8 w9_74 w9_64 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
    -- 0x19A0: j
    obtain ⟨n11, d11, u11⟩ := s10.jump E10.self sv_at_19a0 (off' := 0x1AB8) (by decide)
      (by rw [s10.pc]; decide)
    have s11 : St n11.mem SV n11 0x1AB8 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_9 : reg n11 (9 : Fin 32) = ((0x1B : BitVec 8)).zeroExtend 32 := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = ((0x1B : BitVec 8)).zeroExtend 32 := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x21)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
    have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m11]; exact w10_74
    have b11_3a8 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m11]; exact b10_3a8
    have b11_420 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m11]; exact b10_420
    have b11_421 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = (0x1B : BitVec 8) := by rw [m11]; exact b10_421
    have q11_3a9 : ∀ j, j < 31 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m11]; exact q10_3a9 j hj
    clear q10_3a9 b10_421 b10_420 b10_3a8 w10_74 w10_64 g10_20 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
    exact .inl ⟨(fun ⟨root6', h0', _⟩ => by rw [hr6] at h0'; cases h0'), sv_fail_1ab8 F E11 s11 t11 (fun x hx => (fR11 x hx).trans (fM x hx).symm) V11 hret g11_2 g11_18 hO g11_3 g11_4⟩
  obtain ⟨z6, rb6⟩ := R6
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x21)] := keep_kk5.trans K6
  clear keep_kk5
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K6.w32 (by decide) (by decide)).trans w5_64
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K6.w32 (by decide) (by decide)).trans w5_74
  have b6_3a8 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := (K6.b8 (by decide) (by decide)).trans b5_3a8
  have q6_3a9 : ∀ j, j < 31 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K6.range (by decide) (by decide) j hj).trans (q5_3a9 j hj)
  have b6_420 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := z6
  clear q5_3a9 b5_3a8 w5_74 w5_64 g5_14 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_17 g5_16 g5_15 g5_13 g5_12 g5_11 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  have q6_421 : ∀ j, j < 32 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0) :=
    fun j hj => by rw [← add_ofNat_assoc]; exact memBytes_range rb6 j hj
  -- 0x1994: lbu
  obtain ⟨n7, d7, u7⟩ := s6.lbu E6.self sv_at_1994 (off' := 0x1998) (by decide)
  have s7 : St n7.mem SV n7 0x1998 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
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
  have g7_10 : reg n7 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b6_420]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x21)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m7]; exact w6_74
  have b7_3a8 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m7]; exact b6_3a8
  have b7_420 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m7]; exact b6_420
  have q7_3a9 : ∀ j, j < 31 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m7]; exact q6_3a9 j hj
  have q7_421 : ∀ j, j < 32 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0) := fun j hj => by rw [m7]; exact q6_421 j hj
  clear b6_420 q6_3a9 b6_3a8 w6_74 w6_64 z6 g6_2 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_4 g6_3 V6 E6 fR6 t6 fr6 K6 rk6 sp6 s6 c6
  -- 0x1998: lbu
  have b7_421 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6.getD 0 0) := q7_421 0 (by decide)
  obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_1998 (off' := 0x199C) (by decide)
  have s8 : St n8.mem SV n8 0x199C (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
  have g8_10 : reg n8 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_10]
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
  have g8_9 : reg n8 (9 : Fin 32) = (BitVec.ofNat 8 (root6.getD 0 0)).zeroExtend 32 := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x421 = B + 0x21A0 + BitVec.ofNat 32 0x421 by sv_addr, b7_421]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x21)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
  have b8_3a8 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m8]; exact b7_3a8
  have b8_420 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m8]; exact b7_420
  have b8_421 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6.getD 0 0) := by rw [m8]; exact b7_421
  have q8_3a9 : ∀ j, j < 31 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m8]; exact q7_3a9 j hj
  have q8_421 : ∀ j, j < 32 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0) := fun j hj => by rw [m8]; exact q7_421 j hj
  clear q7_421 q7_3a9 b7_420 b7_3a8 w7_74 w7_64 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7 q6_421
  -- 0x199C: branch, taken
  obtain ⟨n9, d9, u9⟩ := s8.taken E8.self 0x19AA sv_at_199c
    (by decide) (by rw [g8_10, s8.zero]; decide)
  have s9 : St n9.mem SV n9 0x19AA (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
  have g9_9 : reg n9 (9 : Fin 32) = (BitVec.ofNat 8 (root6.getD 0 0)).zeroExtend 32 := by rw [u9.regs, g8_9]
  have g9_10 : reg n9 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u9.regs, g8_10]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [u9.regs, g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [u9.regs, g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x21)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m9]; exact w8_74
  have b9_3a8 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m9]; exact b8_3a8
  have b9_420 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m9]; exact b8_420
  have b9_421 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6.getD 0 0) := by rw [m9]; exact b8_421
  have q9_3a9 : ∀ j, j < 31 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m9]; exact q8_3a9 j hj
  have q9_421 : ∀ j, j < 32 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0) := fun j hj => by rw [m9]; exact q8_421 j hj
  clear q8_421 q8_3a9 b8_421 b8_420 b8_3a8 w8_74 w8_64 g8_9 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8 b7_421
  -- 0x19AA
  obtain ⟨n10, c10, u10⟩ := s9.block svRm19aa E9.self svRm19aa_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x19B6 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svRm19aa (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_9 : reg n10 (9 : Fin 32) = (BitVec.ofNat 8 (root6.getD 0 0)).zeroExtend 32 := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by
    rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_8 : reg n10 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x3A8 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svRm19aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1FD := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svRm19aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_11 : reg n10 a1 = B + 0x21A0 + BitVec.ofNat 32 0x422 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svRm19aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_12 : reg n10 a2 = BitVec.ofNat 32 0x1F := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svRm19aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x21)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
  have b10_3a8 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m10]; exact b9_3a8
  have b10_420 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m10]; exact b9_420
  have b10_421 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6.getD 0 0) := by rw [m10]; exact b9_421
  have q10_3a9 : ∀ j, j < 31 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_3a9 j hj
  have q10_421 : ∀ j, j < 32 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0) := fun j hj => by rw [m10]; exact q9_421 j hj
  clear q9_421 q9_3a9 b9_421 b9_420 b9_3a8 w9_74 w9_64 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x19B6: memcpy
  obtain ⟨n11, P11, K11, X11⟩ := sv_mc (c := 0x1FD) (d := 0x422) (N := 0x1F) F E10 s10 sv_at_19b6 sv_at_19ba
    (by decide) (by decide) g10_2 g10_10 g10_11 g10_12
    (by decide) (by decide) (by decide)
  have s11 := P11.st
  have fr11 := P11.fr
  have t11 : Steps n0 n11 := t10.trans P11.steps
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [P11.regs sp (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P11.regs (3 : Fin 32) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P11.regs (4 : Fin 32) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x3A8 := by rw [P11.regs (8 : Fin 32) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = (BitVec.ofNat 8 (root6.getD 0 0)).zeroExtend 32 := by rw [P11.regs (9 : Fin 32) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [P11.regs (18 : Fin 32) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [P11.regs (19 : Fin 32) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [P11.regs (20 : Fin 32) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [P11.regs (21 : Fin 32) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [P11.regs (22 : Fin 32) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [P11.regs (23 : Fin 32) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [P11.regs (24 : Fin 32) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [P11.regs (25 : Fin 32) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [P11.regs (26 : Fin 32) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [P11.regs (27 : Fin 32) (by decide), g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x21), (0x1FD, 0x1F)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K11.w32 (by decide) (by decide)).trans w10_64
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K11.w32 (by decide) (by decide)).trans w10_74
  have b11_3a8 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_3a8
  have b11_420 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := (K11.b8 (by decide) (by decide)).trans b10_420
  have b11_421 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6.getD 0 0) := (K11.b8 (by decide) (by decide)).trans b10_421
  have q11_3a9 : ∀ j, j < 31 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_3a9 j hj)
  have q11_421 : ∀ j, j < 32 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_421 j hj)
  have q11_1fd : ∀ j, j < 31 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FD + j)) = BitVec.ofNat 8 (root6.getD (1 + j) 0) := fun j hj => by
    rw [show 0x1FD + j = 0x1FD + (0x0 + j) by omega, X11 (0x0 + j) (by omega),
      show 0x422 + (0x0 + j) = 0x421 + (1 + j) by omega]; exact q10_421 (1 + j) (by omega)
  clear q10_421 q10_3a9 b10_421 b10_420 b10_3a8 w10_74 w10_64 g10_12 g10_11 g10_10 g10_8 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x19BE: sb
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sb F E11 s11 sv_at_19be (off' := 0x19C2) (c := 0x1FC)
    (by decide) (by rw [g11_2]; sv_addr) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x3A8 := by rw [rg12 (8 : Fin 32), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = (BitVec.ofNat 8 (root6.getD 0 0)).zeroExtend 32 := by rw [rg12 (9 : Fin 32), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [rg12 (20 : Fin 32), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [rg12 (21 : Fin 32), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [rg12 (22 : Fin 32), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [rg12 (23 : Fin 32), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [rg12 (25 : Fin 32), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [rg12 (27 : Fin 32), g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x21), (0x1FD, 0x1F), (0x1FC, 0x1)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K12.w32 (by decide) (by decide)).trans w11_64
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K12.w32 (by decide) (by decide)).trans w11_74
  have b12_3a8 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := (K12.b8 (by decide) (by decide)).trans b11_3a8
  have b12_420 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := (K12.b8 (by decide) (by decide)).trans b11_420
  have b12_421 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6.getD 0 0) := (K12.b8 (by decide) (by decide)).trans b11_421
  have b12_1fc : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1FC) = BitVec.ofNat 8 (root6.getD 0 0) := by rw [W12, g11_9, lbu_low]
  have q12_1fd : ∀ j, j < 31 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FD + j)) = BitVec.ofNat 8 (root6.getD (1 + j) 0) := fun j hj => (K12.range (by decide) (by decide) j hj).trans (q11_1fd j hj)
  have q12_3a9 : ∀ j, j < 31 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K12.range (by decide) (by decide) j hj).trans (q11_3a9 j hj)
  have q12_421 : ∀ j, j < 32 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0) := fun j hj => (K12.range (by decide) (by decide) j hj).trans (q11_421 j hj)
  clear q11_1fd q11_421 q11_3a9 b11_421 b11_420 b11_3a8 w11_74 w11_64 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 s11 X11 K11 P11
  -- 0x19C2
  obtain ⟨n13, c13, u13⟩ := s12.block svRm19c2 E12.self svRm19c2_end
    ⟨trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x19C6 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svRm19c2 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by
    rw [rb13, runBlock_reg _ _ _ sp s12.zero (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb13, runBlock_reg _ _ _ (3 : Fin 32) s12.zero (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb13, runBlock_reg _ _ _ (4 : Fin 32) s12.zero (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x3A8 := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = (BitVec.ofNat 8 (root6.getD 0 0)).zeroExtend 32 := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by
    rw [rb13, runBlock_reg _ _ _ (20 : Fin 32) s12.zero (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1FC := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svRm19c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g13_11 : reg n13 a1 = B + 0x21A0 + BitVec.ofNat 32 0x3A8 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svRm19c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x21), (0x1FD, 0x1F), (0x1FC, 0x1)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m13]; exact w12_64
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m13]; exact w12_74
  have b13_1fc : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1FC) = BitVec.ofNat 8 (root6.getD 0 0) := by rw [m13]; exact b12_1fc
  have b13_3a8 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m13]; exact b12_3a8
  have b13_420 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m13]; exact b12_420
  have b13_421 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6.getD 0 0) := by rw [m13]; exact b12_421
  have q13_1fd : ∀ j, j < 31 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FD + j)) = BitVec.ofNat 8 (root6.getD (1 + j) 0) := fun j hj => by rw [m13]; exact q12_1fd j hj
  have q13_3a9 : ∀ j, j < 31 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m13]; exact q12_3a9 j hj
  have q13_421 : ∀ j, j < 32 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0) := fun j hj => by rw [m13]; exact q12_421 j hj
  clear q12_421 q12_3a9 q12_1fd b12_1fc b12_421 b12_420 b12_3a8 w12_74 w12_64 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0x19C6: sv_a32eqF
  obtain ⟨n14, c14, s14, sp14, rk14, a0_14, K14, fr14⟩ := sv_a32eqF (oc := 0x1FC) (oc2 := 0x3A8)
    F E13 s13 sv_at_19c6 sv_at_19ca (by decide) (by decide) g13_2
    g13_10 g13_11 (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans c14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keepL K14 (by decide)
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk14 (3 : Fin 32) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk14 (4 : Fin 32) (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x3A8 := by rw [rk14 (8 : Fin 32) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = (BitVec.ofNat 8 (root6.getD 0 0)).zeroExtend 32 := by rw [rk14 (9 : Fin 32) (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rk14 (18 : Fin 32) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rk14 (19 : Fin 32) (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [rk14 (20 : Fin 32) (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rk14 (21 : Fin 32) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [rk14 (22 : Fin 32) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [rk14 (23 : Fin 32) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [rk14 (24 : Fin 32) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [rk14 (25 : Fin 32) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rk14 (26 : Fin 32) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by rw [rk14 (27 : Fin 32) (by decide), g13_27]
  have g14_2 : reg n14 sp = B + 0x21A0 := sp14
  rw [join32 b13_1fc q13_1fd, join32 (b13_3a8.trans (zext_lo8 _)) q13_3a9] at a0_14
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x21), (0x1FD, 0x1F), (0x1FC, 0x1)] := keep_kk13.trans K14
  clear keep_kk13
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K14.w32 (by decide) (by decide)).trans w13_64
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K14.w32 (by decide) (by decide)).trans w13_74
  have b14_1fc : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1FC) = BitVec.ofNat 8 (root6.getD 0 0) := (K14.b8 (by decide) (by decide)).trans b13_1fc
  have b14_3a8 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := (K14.b8 (by decide) (by decide)).trans b13_3a8
  have b14_420 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := (K14.b8 (by decide) (by decide)).trans b13_420
  have b14_421 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6.getD 0 0) := (K14.b8 (by decide) (by decide)).trans b13_421
  have q14_1fd : ∀ j, j < 31 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FD + j)) = BitVec.ofNat 8 (root6.getD (1 + j) 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_1fd j hj)
  have q14_3a9 : ∀ j, j < 31 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_3a9 j hj)
  have q14_421 : ∀ j, j < 32 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_421 j hj)
  clear q13_421 q13_3a9 q13_1fd b13_421 b13_420 b13_3a8 b13_1fc w13_74 w13_64 g13_11 g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  by_cases hroot : b32 root6 = b32 rt
  rotate_left
  · have g14_10 : reg n14 a0 = BitVec.ofNat 32 0 := by rw [a0_14, ite_eq_right hroot]; rfl
    -- 0x19CE: branch, taken
    obtain ⟨n15, d15, u15⟩ := s14.taken E14.self 0x1AB8 sv_at_19ce
      (by decide) (by rw [g14_10, s14.zero]; decide)
    have s15 : St n15.mem SV n15 0x1AB8 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
    have t15 : Steps n0 n15 := t14.trans (.single d15)
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.same m15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
    have g15_8 : reg n15 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x3A8 := by rw [u15.regs, g14_8]
    have g15_9 : reg n15 (9 : Fin 32) = (BitVec.ofNat 8 (root6.getD 0 0)).zeroExtend 32 := by rw [u15.regs, g14_9]
    have g15_10 : reg n15 a0 = BitVec.ofNat 32 0x0 := by rw [u15.regs, g14_10]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
    have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
    have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, g14_27]
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x21), (0x1FD, 0x1F), (0x1FC, 0x1)] := by rw [m15]; exact keep_kk14
    clear keep_kk14
    have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
    have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m15]; exact w14_74
    have b15_1fc : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1FC) = BitVec.ofNat 8 (root6.getD 0 0) := by rw [m15]; exact b14_1fc
    have b15_3a8 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m15]; exact b14_3a8
    have b15_420 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m15]; exact b14_420
    have b15_421 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6.getD 0 0) := by rw [m15]; exact b14_421
    have q15_1fd : ∀ j, j < 31 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FD + j)) = BitVec.ofNat 8 (root6.getD (1 + j) 0) := fun j hj => by rw [m15]; exact q14_1fd j hj
    have q15_3a9 : ∀ j, j < 31 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m15]; exact q14_3a9 j hj
    have q15_421 : ∀ j, j < 32 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0) := fun j hj => by rw [m15]; exact q14_421 j hj
    clear q14_421 q14_3a9 q14_1fd b14_421 b14_420 b14_3a8 b14_1fc w14_74 w14_64 g14_2 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 V14 E14 fR14 t14 fr14 K14 a0_14 rk14 sp14 s14 c14
    exact .inl ⟨(fun ⟨root6', h0', h1', _⟩ => by rw [hr6] at h0'; cases h0'; exact hroot h1'), sv_fail_1ab8 F E15 s15 t15 (fun x hx => (fR15 x hx).trans (fM x hx).symm) V15 hret g15_2 g15_18 hO g15_3 g15_4⟩
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 1 := by rw [a0_14, ite_eq_left hroot]; rfl
  -- 0x19CE: branch, not taken
  obtain ⟨n15, d15, u15⟩ := s14.notTaken E14.self 0x19D0 sv_at_19ce
    (by decide) (by rw [g14_10, s14.zero]; decide)
  have s15 : St n15.mem SV n15 0x19D0 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x3A8 := by rw [u15.regs, g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = (BitVec.ofNat 8 (root6.getD 0 0)).zeroExtend 32 := by rw [u15.regs, g14_9]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 0x1 := by rw [u15.regs, g14_10]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x21), (0x1FD, 0x1F), (0x1FC, 0x1)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m15]; exact w14_74
  have b15_1fc : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1FC) = BitVec.ofNat 8 (root6.getD 0 0) := by rw [m15]; exact b14_1fc
  have b15_3a8 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 := by rw [m15]; exact b14_3a8
  have b15_420 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m15]; exact b14_420
  have b15_421 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6.getD 0 0) := by rw [m15]; exact b14_421
  have q15_1fd : ∀ j, j < 31 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FD + j)) = BitVec.ofNat 8 (root6.getD (1 + j) 0) := fun j hj => by rw [m15]; exact q14_1fd j hj
  have q15_3a9 : ∀ j, j < 31 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m15]; exact q14_3a9 j hj
  have q15_421 : ∀ j, j < 32 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root6.getD j 0) := fun j hj => by rw [m15]; exact q14_421 j hj
  clear q14_421 q14_3a9 q14_1fd b14_421 b14_420 b14_3a8 b14_1fc w14_74 w14_64 g14_2 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 V14 E14 fR14 t14 fr14 K14 a0_14 rk14 sp14 s14 c14
  exact .inr ⟨root6, hr6, hroot, n15, t15, s15, E15, V15, fR15, g15_2, g15_3, g15_4, g15_8, g15_9, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, w15_64, w15_74, b15_1fc, b15_3a8, b15_420, b15_421, q15_1fd, q15_3a9, q15_421, keep_kk15.mono (by decide)⟩

end C3.RV32.Sv
