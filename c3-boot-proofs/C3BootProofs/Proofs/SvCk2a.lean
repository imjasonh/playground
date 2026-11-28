import C3BootProofs.Proofs.SvCkpt

/-!
# `sigstore::verify`: the checkpoint's size line

From 0x14C2 to the size's digit loop at 0x14FE: the signature section is shorter than the checkpoint, the size line has 1 to 20 bytes, and it has one byte.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCk2a1878 : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x1A]
theorem svCk2a1878_end : blockEnd sigstoreVerifyCode 0x1878 svCk2a1878 = some 0x187A := by
  simp only [svCk2a1878]
  rw [blockEnd, sv_at_1878]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk2a14ca : List BInstr :=
  [.aluImm .xor a0 a0 0xFFFFFFFF]
theorem svCk2a14ca_end : blockEnd sigstoreVerifyCode 0x14CA svCk2a14ca = some 0x14CE := by
  simp only [svCk2a14ca]
  rw [blockEnd, sv_at_14ca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk2a14ce : List BInstr :=
  [.alu .add a0 a0 (9 : Fin 32)]
theorem svCk2a14ce_end : blockEnd sigstoreVerifyCode 0x14CE svCk2a14ce = some 0x14D0 := by
  simp only [svCk2a14ce]
  rw [blockEnd, sv_at_14ce]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk2a14d6 : List BInstr :=
  [.aluImm .add a0 (8 : Fin 32) 0xFFFFFFEC]
theorem svCk2a14d6_end : blockEnd sigstoreVerifyCode 0x14D6 svCk2a14d6 = some 0x14DA := by
  simp only [svCk2a14d6]
  rw [blockEnd, sv_at_14d6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk2a14da : List BInstr :=
  [.aluImm .add a1 x0 0xFFFFFFED]
theorem svCk2a14da_end : blockEnd sigstoreVerifyCode 0x14DA svCk2a14da = some 0x14DC := by
  simp only [svCk2a14da]
  rw [blockEnd, sv_at_14da]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk2a14e6 : List BInstr :=
  [.aluImm .add a0 x0 0x1]
theorem svCk2a14e6_end : blockEnd sigstoreVerifyCode 0x14E6 svCk2a14e6 = some 0x14E8 := by
  simp only [svCk2a14e6]
  rw [blockEnd, sv_at_14e6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk2a14fc : List BInstr :=
  [.aluImm .add a0 x0 0xA]
theorem svCk2a14fc_end : blockEnd sigstoreVerifyCode 0x14FC svCk2a14fc = some 0x14FE := by
  simp only [svCk2a14fc]
  rw [blockEnd, sv_at_14fc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_ck2a {B out bp x20 x21 x22 x23 x26 ckl sl sp1 rl rp sgp w50 : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x14C2 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = sl)
    (g0_9 : reg n0 (9 : Fin 32) = ckl)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = sp1)
    (g0_25 : reg n0 (25 : Fin 32) = rp)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = rl)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (w0_428 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp)
    (sz_in : SvIn B sp1 sl.toNat)
    (hsl : ¬ 1 < sl.toNat) :
    (¬ ((w50.toNat < ckl.toNat) ∧ (¬ (ckl).toNat < ((aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)).toNat) ∧ (¬ ((sl) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((w50.toNat < ckl.toNat) ∧
    (¬ (ckl).toNat < ((aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)).toNat) ∧
    (¬ ((sl) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x14FE (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = sl ∧
        reg n' (9 : Fin 32) = ckl ∧
        reg n' a0 = BitVec.ofNat 32 0xA ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = sp1 ∧
        reg n' (25 : Fin 32) = rp ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = rl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sgp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp ∧
        SvKeepL B n0.mem n'.mem [(0x24, 0x4), (0x38, 0x4), (0x64, 0x4), (0x74, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x14C2: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_14c2 (off' := 0x14C4) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0x14C4 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = sl := by rw [u1.regs, upd_ne (by decide) (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = ckl := by rw [u1.regs, upd_ne (by decide) (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, upd_ne (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = sp1 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = rp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = rl := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_10 : reg n1 a0 = w50 := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w0_50]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  have w1_428 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m1]; exact w0_428
  by_cases hc1 : w50.toNat < ckl.toNat
  rotate_left
  · -- 0x14C4: branch, taken
    obtain ⟨n2, d2, u2⟩ := s1.taken E1.self 0x1878 sv_at_14c4
      (by decide) (by rw [g1_10, g1_9]; exact br_bgeu_t hc1)
    have s2 : St n2.mem SV n2 0x1878 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
    have m2 : n2.mem = n1.mem := u2.mem
    have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
    have t2 : Steps n0 n2 := t1.trans (.single d2)
    have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
    have E2 : SvCode n2.mem := E1.fr F fr2
    have V2 : SvSaves B n2.mem v := V1.same m2
    have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, g1_2]
    have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, g1_3]
    have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, g1_4]
    have g2_8 : reg n2 (8 : Fin 32) = sl := by rw [u2.regs, g1_8]
    have g2_9 : reg n2 (9 : Fin 32) = ckl := by rw [u2.regs, g1_9]
    have g2_10 : reg n2 a0 = w50 := by rw [u2.regs, g1_10]
    have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, g1_18]
    have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, g1_19]
    have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [u2.regs, g1_20]
    have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, g1_21]
    have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [u2.regs, g1_22]
    have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [u2.regs, g1_23]
    have g2_24 : reg n2 (24 : Fin 32) = sp1 := by rw [u2.regs, g1_24]
    have g2_25 : reg n2 (25 : Fin 32) = rp := by rw [u2.regs, g1_25]
    have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, g1_26]
    have g2_27 : reg n2 (27 : Fin 32) = rl := by rw [u2.regs, g1_27]
    have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
    clear keep_kk1
    have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
    have w2_428 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m2]; exact w1_428
    clear w1_428 w1_50 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
    -- 0x1878
    obtain ⟨n3, c3, u3⟩ := s2.block svCk2a1878 E2.self svCk2a1878_end
      ⟨trivial, trivial⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have s3 : St n3.mem SV n3 0x187A (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have rb3 : ∀ q, reg n3 q = (runBlock svCk2a1878 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
    have g3_8 : reg n3 (8 : Fin 32) = sl := by
      rw [rb3, runBlock_reg _ _ _ (8 : Fin 32) s2.zero (by decide), g2_8]
    have g3_9 : reg n3 (9 : Fin 32) = ckl := by
      rw [rb3, runBlock_reg _ _ _ (9 : Fin 32) s2.zero (by decide), g2_9]
    have g3_10 : reg n3 a0 = w50 := by
      rw [rb3, runBlock_reg _ _ _ a0 s2.zero (by decide), g2_10]
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
    have g3_24 : reg n3 (24 : Fin 32) = sp1 := by
      rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
    have g3_26 : reg n3 (26 : Fin 32) = x26 := by
      rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = rl := by
      rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
    have g3_25 : reg n3 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb3]; simp +decide only [runBlock, BInstr.run, svCk2a1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_9, g2_10, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
    have w3_428 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m3]; exact w2_428
    clear w2_428 w2_50 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
    -- 0x187A: j
    obtain ⟨n4, d4, u4⟩ := s3.jump E3.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s3.pc]; decide)
    have s4 : St n4.mem SV n4 0x1882 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
    have g4_8 : reg n4 (8 : Fin 32) = sl := by rw [u4.regs, g3_8]
    have g4_9 : reg n4 (9 : Fin 32) = ckl := by rw [u4.regs, g3_9]
    have g4_10 : reg n4 a0 = w50 := by rw [u4.regs, g3_10]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, g3_20]
    have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, g3_22]
    have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, g3_23]
    have g4_24 : reg n4 (24 : Fin 32) = sp1 := by rw [u4.regs, g3_24]
    have g4_25 : reg n4 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u4.regs, g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = rl := by rw [u4.regs, g3_27]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m4]; exact w3_50
    have w4_428 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m4]; exact w3_428
    clear w3_428 w3_50 g3_25 g3_27 g3_26 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hc1 h0'), sv_fail_1882 F E4 s4 t4 (fun x hx => (fR4 x hx).trans (fM x hx).symm) V4 hret g4_2 g4_18 hO g4_3 g4_4 (by rw [g4_25]; sv_code)⟩
  -- 0x14C4: branch, not taken
  obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.self 0x14C8 sv_at_14c4
    (by decide) (by rw [g1_10, g1_9]; exact br_bgeu_f hc1)
  have s2 : St n2.mem SV n2 0x14C8 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = sl := by rw [u2.regs, g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = ckl := by rw [u2.regs, g1_9]
  have g2_10 : reg n2 a0 = w50 := by rw [u2.regs, g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [u2.regs, g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [u2.regs, g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [u2.regs, g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = sp1 := by rw [u2.regs, g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = rp := by rw [u2.regs, g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = rl := by rw [u2.regs, g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
  have w2_428 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m2]; exact w1_428
  clear w1_428 w1_50 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x14C8: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_14c8 (off' := 0x14CA) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x14CA (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = sl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = ckl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = sp1 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = rp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = rl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_10 : reg n3 a0 = w50 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w2_50]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  have w3_428 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m3]; exact w2_428
  clear w2_428 w2_50 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x14CA
  obtain ⟨n4, c4, u4⟩ := s3.block svCk2a14ca E3.self svCk2a14ca_end
    ⟨trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x14CE (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svCk2a14ca (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_8 : reg n4 (8 : Fin 32) = sl := by
    rw [rb4, runBlock_reg _ _ _ (8 : Fin 32) s3.zero (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = ckl := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
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
  have g4_24 : reg n4 (24 : Fin 32) = sp1 := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = rp := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = rl := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_10 : reg n4 a0 = aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF) := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svCk2a14ca, upd, ↓reduceIte]; rw [g3_10] <;> rfl
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m4]; exact w3_50
  have w4_428 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m4]; exact w3_428
  clear w3_428 w3_50 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x14CE
  obtain ⟨n5, c5, u5⟩ := s4.block svCk2a14ce E4.self svCk2a14ce_end
    ⟨trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x14D0 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svCk2a14ce (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_8 : reg n5 (8 : Fin 32) = sl := by
    rw [rb5, runBlock_reg _ _ _ (8 : Fin 32) s4.zero (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = ckl := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
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
  have g5_24 : reg n5 (24 : Fin 32) = sp1 := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = rp := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = rl := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svCk2a14ce, upd, ↓reduceIte]; rw [g4_10, g4_9] <;> rfl
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have w5_428 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m5]; exact w4_428
  clear w4_428 w4_50 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x14D0: sw
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := sv_sw F E5 s5 sv_at_14d0 (off' := 0x14D2) (c := 0x24)
    (by decide) (by rw [g5_2]; sv_addr) (by decide) (by decide)
  have t6 : Steps n0 n6 := t5.trans d6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rg6 sp, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg6 (3 : Fin 32), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg6 (4 : Fin 32), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = sl := by rw [rg6 (8 : Fin 32), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = ckl := by rw [rg6 (9 : Fin 32), g5_9]
  have g6_10 : reg n6 a0 = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [rg6 a0, g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [rg6 (18 : Fin 32), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [rg6 (19 : Fin 32), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [rg6 (20 : Fin 32), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [rg6 (21 : Fin 32), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [rg6 (22 : Fin 32), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [rg6 (23 : Fin 32), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = sp1 := by rw [rg6 (24 : Fin 32), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = rp := by rw [rg6 (25 : Fin 32), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [rg6 (26 : Fin 32), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = rl := by rw [rg6 (27 : Fin 32), g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x24, 0x4)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K6.w32 (by decide) (by decide)).trans w5_50
  have w6_428 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := (K6.w32 (by decide) (by decide)).trans w5_428
  have w6_24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [W6, g5_10]
  clear w5_428 w5_50 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  by_cases hc2 : ¬ (ckl).toNat < ((aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)).toNat
  rotate_left
  · -- 0x14D2: branch, taken
    obtain ⟨n7, d7, u7⟩ := s6.taken E6.self 0x1878 sv_at_14d2
      (by decide) (by rw [g6_9, g6_10]; exact br_bltu_t (Decidable.of_not_not hc2))
    have s7 : St n7.mem SV n7 0x1878 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
    have g7_8 : reg n7 (8 : Fin 32) = sl := by rw [u7.regs, g6_8]
    have g7_9 : reg n7 (9 : Fin 32) = ckl := by rw [u7.regs, g6_9]
    have g7_10 : reg n7 a0 = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [u7.regs, g6_10]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = sp1 := by rw [u7.regs, g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = rp := by rw [u7.regs, g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = rl := by rw [u7.regs, g6_27]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x24, 0x4)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m7]; exact w6_24
    have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
    have w7_428 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m7]; exact w6_428
    clear w6_24 w6_428 w6_50 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
    -- 0x1878
    obtain ⟨n8, c8, u8⟩ := s7.block svCk2a1878 E7.self svCk2a1878_end
      ⟨trivial, trivial⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have s8 : St n8.mem SV n8 0x187A (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have rb8 : ∀ q, reg n8 q = (runBlock svCk2a1878 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
    have g8_8 : reg n8 (8 : Fin 32) = sl := by
      rw [rb8, runBlock_reg _ _ _ (8 : Fin 32) s7.zero (by decide), g7_8]
    have g8_9 : reg n8 (9 : Fin 32) = ckl := by
      rw [rb8, runBlock_reg _ _ _ (9 : Fin 32) s7.zero (by decide), g7_9]
    have g8_10 : reg n8 a0 = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by
      rw [rb8, runBlock_reg _ _ _ a0 s7.zero (by decide), g7_10]
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
    have g8_24 : reg n8 (24 : Fin 32) = sp1 := by
      rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
    have g8_26 : reg n8 (26 : Fin 32) = x26 := by
      rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = rl := by
      rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
    have g8_25 : reg n8 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb8]; simp +decide only [runBlock, BInstr.run, svCk2a1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x24, 0x4)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m8]; exact w7_24
    have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
    have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m8]; exact w7_428
    clear w7_428 w7_50 w7_24 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
    -- 0x187A: j
    obtain ⟨n9, d9, u9⟩ := s8.jump E8.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s8.pc]; decide)
    have s9 : St n9.mem SV n9 0x1882 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = sl := by rw [u9.regs, g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = ckl := by rw [u9.regs, g8_9]
    have g9_10 : reg n9 a0 = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [u9.regs, g8_10]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = sp1 := by rw [u9.regs, g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u9.regs, g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = rl := by rw [u9.regs, g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x24, 0x4)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m9]; exact w8_24
    have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
    have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m9]; exact w8_428
    clear w8_428 w8_50 w8_24 g8_25 g8_27 g8_26 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
    exact .inl ⟨(fun ⟨h0', h1', _⟩ => by exact hc2 h1'), sv_fail_1882 F E9 s9 t9 (fun x hx => (fR9 x hx).trans (fM x hx).symm) V9 hret g9_2 g9_18 hO g9_3 g9_4 (by rw [g9_25]; sv_code)⟩
  -- 0x14D2: branch, not taken
  obtain ⟨n7, d7, u7⟩ := s6.notTaken E6.self 0x14D6 sv_at_14d2
    (by decide) (by rw [g6_9, g6_10]; exact br_bltu_f hc2)
  have s7 : St n7.mem SV n7 0x14D6 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = sl := by rw [u7.regs, g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = ckl := by rw [u7.regs, g6_9]
  have g7_10 : reg n7 a0 = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [u7.regs, g6_10]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = sp1 := by rw [u7.regs, g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = rp := by rw [u7.regs, g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = rl := by rw [u7.regs, g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x24, 0x4)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m7]; exact w6_24
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
  have w7_428 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m7]; exact w6_428
  clear w6_24 w6_428 w6_50 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
  -- 0x14D6
  obtain ⟨n8, c8, u8⟩ := s7.block svCk2a14d6 E7.self svCk2a14d6_end
    ⟨trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x14DA (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svCk2a14d6 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_8 : reg n8 (8 : Fin 32) = sl := by
    rw [rb8, runBlock_reg _ _ _ (8 : Fin 32) s7.zero (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = ckl := by
    rw [rb8, runBlock_reg _ _ _ (9 : Fin 32) s7.zero (by decide), g7_9]
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
  have g8_24 : reg n8 (24 : Fin 32) = sp1 := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = rp := by
    rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = rl := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_10 : reg n8 a0 = (sl) + BitVec.ofNat 32 0xFFFFFFEC := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svCk2a14d6, upd, ↓reduceIte]; rw [g7_8] <;> rfl
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x24, 0x4)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m8]; exact w7_24
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
  have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m8]; exact w7_428
  clear w7_428 w7_50 w7_24 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x14DA
  obtain ⟨n9, c9, u9⟩ := s8.block svCk2a14da E8.self svCk2a14da_end
    ⟨trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0x14DC (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svCk2a14da (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_8 : reg n9 (8 : Fin 32) = sl := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = ckl := by
    rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
  have g9_10 : reg n9 a0 = (sl) + BitVec.ofNat 32 0xFFFFFFEC := by
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
  have g9_24 : reg n9 (24 : Fin 32) = sp1 := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = rp := by
    rw [rb9, runBlock_reg _ _ _ (25 : Fin 32) s8.zero (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = rl := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_11 : reg n9 a1 = BitVec.ofNat 32 0xFFFFFFED := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svCk2a14da, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals (try simp only [BitVec.ofNat_eq_ofNat])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x24, 0x4)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m9]; exact w8_24
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m9]; exact w8_428
  clear w8_428 w8_50 w8_24 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  by_cases hc3 : ¬ ((sl) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat
  rotate_left
  · -- 0x14DC: branch, taken
    obtain ⟨n10, d10, u10⟩ := s9.taken E9.self 0x1878 sv_at_14dc
      (by decide) (by rw [g9_10, g9_11]; exact br_bltu_t (Decidable.of_not_not hc3))
    have s10 : St n10.mem SV n10 0x1878 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = sl := by rw [u10.regs, g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = ckl := by rw [u10.regs, g9_9]
    have g10_10 : reg n10 a0 = (sl) + BitVec.ofNat 32 0xFFFFFFEC := by rw [u10.regs, g9_10]
    have g10_11 : reg n10 a1 = BitVec.ofNat 32 0xFFFFFFED := by rw [u10.regs, g9_11]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [u10.regs, g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = sp1 := by rw [u10.regs, g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = rp := by rw [u10.regs, g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = rl := by rw [u10.regs, g9_27]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x24, 0x4)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m10]; exact w9_24
    have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
    have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m10]; exact w9_428
    clear w9_428 w9_50 w9_24 g9_11 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
    -- 0x1878
    obtain ⟨n11, c11, u11⟩ := s10.block svCk2a1878 E10.self svCk2a1878_end
      ⟨trivial, trivial⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have s11 : St n11.mem SV n11 0x187A (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have rb11 : ∀ q, reg n11 q = (runBlock svCk2a1878 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
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
    have g11_8 : reg n11 (8 : Fin 32) = sl := by
      rw [rb11, runBlock_reg _ _ _ (8 : Fin 32) s10.zero (by decide), g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = ckl := by
      rw [rb11, runBlock_reg _ _ _ (9 : Fin 32) s10.zero (by decide), g10_9]
    have g11_10 : reg n11 a0 = (sl) + BitVec.ofNat 32 0xFFFFFFEC := by
      rw [rb11, runBlock_reg _ _ _ a0 s10.zero (by decide), g10_10]
    have g11_11 : reg n11 a1 = BitVec.ofNat 32 0xFFFFFFED := by
      rw [rb11, runBlock_reg _ _ _ a1 s10.zero (by decide), g10_11]
    have g11_18 : reg n11 (18 : Fin 32) = out := by
      rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by
      rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = x20 := by
      rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by
      rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by
      rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by
      rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = sp1 := by
      rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by
      rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = rl := by
      rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
    have g11_25 : reg n11 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb11]; simp +decide only [runBlock, BInstr.run, svCk2a1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_9, g10_10, g10_11, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_25, g10_26, g10_27, s10.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x24, 0x4)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m11]; exact w10_24
    have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
    have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m11]; exact w10_428
    clear w10_428 w10_50 w10_24 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_11 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x187A: j
    obtain ⟨n12, d12, u12⟩ := s11.jump E11.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s11.pc]; decide)
    have s12 : St n12.mem SV n12 0x1882 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
    have g12_8 : reg n12 (8 : Fin 32) = sl := by rw [u12.regs, g11_8]
    have g12_9 : reg n12 (9 : Fin 32) = ckl := by rw [u12.regs, g11_9]
    have g12_10 : reg n12 a0 = (sl) + BitVec.ofNat 32 0xFFFFFFEC := by rw [u12.regs, g11_10]
    have g12_11 : reg n12 a1 = BitVec.ofNat 32 0xFFFFFFED := by rw [u12.regs, g11_11]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = sp1 := by rw [u12.regs, g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u12.regs, g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = rl := by rw [u12.regs, g11_27]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x24, 0x4)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m12]; exact w11_24
    have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
    have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m12]; exact w11_428
    clear w11_428 w11_50 w11_24 g11_25 g11_27 g11_26 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_11 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
    exact .inl ⟨(fun ⟨h0', h1', h2', _⟩ => by exact hc3 h2'), sv_fail_1882 F E12 s12 t12 (fun x hx => (fR12 x hx).trans (fM x hx).symm) V12 hret g12_2 g12_18 hO g12_3 g12_4 (by rw [g12_25]; sv_code)⟩
  -- 0x14DC: branch, not taken
  obtain ⟨n10, d10, u10⟩ := s9.notTaken E9.self 0x14E0 sv_at_14dc
    (by decide) (by rw [g9_10, g9_11]; exact br_bltu_f hc3)
  have s10 : St n10.mem SV n10 0x14E0 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = sl := by rw [u10.regs, g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = ckl := by rw [u10.regs, g9_9]
  have g10_10 : reg n10 a0 = (sl) + BitVec.ofNat 32 0xFFFFFFEC := by rw [u10.regs, g9_10]
  have g10_11 : reg n10 a1 = BitVec.ofNat 32 0xFFFFFFED := by rw [u10.regs, g9_11]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [u10.regs, g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = sp1 := by rw [u10.regs, g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = rp := by rw [u10.regs, g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = rl := by rw [u10.regs, g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x24, 0x4)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m10]; exact w9_24
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m10]; exact w9_428
  clear w9_428 w9_50 w9_24 g9_11 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x14E0: lw
  obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_14e0 (off' := 0x14E4) (by decide)
    (by rw [g10_2, show B + 0x21A0 + 0x428 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s11 : St n11.mem SV n11 0x14E4 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = sl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = ckl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
  have g11_11 : reg n11 a1 = BitVec.ofNat 32 0xFFFFFFED := by rw [u11.regs, upd_ne (by decide) (by decide), g10_11]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = sp1 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = rp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = rl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
  have g11_10 : reg n11 a0 = sgp := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g10_2, show B + 0x21A0 + 0x428 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w10_428]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x24, 0x4)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m11]; exact w10_24
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m11]; exact w10_428
  clear w10_428 w10_50 w10_24 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_11 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x14E4: sw
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sw F E11 s11 sv_at_14e4 (off' := 0x14E6) (c := 0x38)
    (by decide) (by rw [g11_2]; sv_addr) (by decide) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = sl := by rw [rg12 (8 : Fin 32), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = ckl := by rw [rg12 (9 : Fin 32), g11_9]
  have g12_10 : reg n12 a0 = sgp := by rw [rg12 a0, g11_10]
  have g12_11 : reg n12 a1 = BitVec.ofNat 32 0xFFFFFFED := by rw [rg12 a1, g11_11]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [rg12 (20 : Fin 32), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [rg12 (21 : Fin 32), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [rg12 (22 : Fin 32), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [rg12 (23 : Fin 32), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = sp1 := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = rp := by rw [rg12 (25 : Fin 32), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = rl := by rw [rg12 (27 : Fin 32), g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x24, 0x4), (0x38, 0x4)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := (K12.w32 (by decide) (by decide)).trans w11_24
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K12.w32 (by decide) (by decide)).trans w11_50
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := (K12.w32 (by decide) (by decide)).trans w11_428
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sgp := by rw [W12, g11_10]
  clear w11_428 w11_50 w11_24 g11_10 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_11 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x14E6
  obtain ⟨n13, c13, u13⟩ := s12.block svCk2a14e6 E12.self svCk2a14e6_end
    ⟨trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x14E8 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svCk2a14e6 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_8 : reg n13 (8 : Fin 32) = sl := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = ckl := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 0xFFFFFFED := by
    rw [rb13, runBlock_reg _ _ _ a1 s12.zero (by decide), g12_11]
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
  have g13_24 : reg n13 (24 : Fin 32) = sp1 := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = rp := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = rl := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_10 : reg n13 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svCk2a14e6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_10, g12_11, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x24, 0x4), (0x38, 0x4)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m13]; exact w12_24
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sgp := by rw [m13]; exact w12_38
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m13]; exact w12_428
  clear w12_38 w12_428 w12_50 w12_24 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_11 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0x14E8: branch, taken
  obtain ⟨n14, d14, u14⟩ := s13.taken E13.self 0x14F8 sv_at_14e8
    (by decide) (by rw [g13_10, g13_8]; exact br_bgeu_t hsl)
  have s14 : St n14.mem SV n14 0x14F8 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = sl := by rw [u14.regs, g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = ckl := by rw [u14.regs, g13_9]
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 0x1 := by rw [u14.regs, g13_10]
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 0xFFFFFFED := by rw [u14.regs, g13_11]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [u14.regs, g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [u14.regs, g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [u14.regs, g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [u14.regs, g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = sp1 := by rw [u14.regs, g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = rp := by rw [u14.regs, g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [u14.regs, g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = rl := by rw [u14.regs, g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x24, 0x4), (0x38, 0x4)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m14]; exact w13_24
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sgp := by rw [m14]; exact w13_38
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m14]; exact w13_50
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m14]; exact w13_428
  clear w13_428 w13_50 w13_38 w13_24 g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_11 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x14F8: sw
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sw F E14 s14 sv_at_14f8 (off' := 0x14FA) (c := 0x64)
    (by decide) (by rw [g14_2]; sv_addr) (by decide) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = sl := by rw [rg15 (8 : Fin 32), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = ckl := by rw [rg15 (9 : Fin 32), g14_9]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 0x1 := by rw [rg15 a0, g14_10]
  have g15_11 : reg n15 a1 = BitVec.ofNat 32 0xFFFFFFED := by rw [rg15 a1, g14_11]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rg15 (18 : Fin 32), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rg15 (19 : Fin 32), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [rg15 (20 : Fin 32), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [rg15 (21 : Fin 32), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [rg15 (22 : Fin 32), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [rg15 (23 : Fin 32), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = sp1 := by rw [rg15 (24 : Fin 32), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = rp := by rw [rg15 (25 : Fin 32), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [rg15 (26 : Fin 32), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = rl := by rw [rg15 (27 : Fin 32), g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x24, 0x4), (0x38, 0x4), (0x64, 0x4)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := (K15.w32 (by decide) (by decide)).trans w14_24
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sgp := (K15.w32 (by decide) (by decide)).trans w14_38
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K15.w32 (by decide) (by decide)).trans w14_50
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := (K15.w32 (by decide) (by decide)).trans w14_428
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [W15, s14.zero]; rfl
  clear w14_428 w14_50 w14_38 w14_24 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_11 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0x14FA: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_14fa (off' := 0x14FC) (c := 0x74)
    (by decide) (by rw [g15_2]; sv_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = sl := by rw [rg16 (8 : Fin 32), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = ckl := by rw [rg16 (9 : Fin 32), g15_9]
  have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x1 := by rw [rg16 a0, g15_10]
  have g16_11 : reg n16 a1 = BitVec.ofNat 32 0xFFFFFFED := by rw [rg16 a1, g15_11]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [rg16 (20 : Fin 32), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [rg16 (21 : Fin 32), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [rg16 (22 : Fin 32), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [rg16 (23 : Fin 32), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = sp1 := by rw [rg16 (24 : Fin 32), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = rp := by rw [rg16 (25 : Fin 32), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [rg16 (26 : Fin 32), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = rl := by rw [rg16 (27 : Fin 32), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x24, 0x4), (0x38, 0x4), (0x64, 0x4), (0x74, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := (K16.w32 (by decide) (by decide)).trans w15_24
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sgp := (K16.w32 (by decide) (by decide)).trans w15_38
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K16.w32 (by decide) (by decide)).trans w15_50
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := (K16.w32 (by decide) (by decide)).trans w15_64
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := (K16.w32 (by decide) (by decide)).trans w15_428
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 0x0 := by rw [W16, s15.zero]; rfl
  clear w15_64 w15_428 w15_50 w15_38 w15_24 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_11 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  -- 0x14FC
  obtain ⟨n17, c17, u17⟩ := s16.block svCk2a14fc E16.self svCk2a14fc_end
    ⟨trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x14FE (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svCk2a14fc (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_8 : reg n17 (8 : Fin 32) = sl := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = ckl := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_11 : reg n17 a1 = BitVec.ofNat 32 0xFFFFFFED := by
    rw [rb17, runBlock_reg _ _ _ a1 s16.zero (by decide), g16_11]
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
  have g17_24 : reg n17 (24 : Fin 32) = sp1 := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = rp := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = rl := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = BitVec.ofNat 32 0xA := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svCk2a14fc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_11, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x24, 0x4), (0x38, 0x4), (0x64, 0x4), (0x74, 0x4)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) := by rw [m17]; exact w16_24
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sgp := by rw [m17]; exact w16_38
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m17]; exact w16_64
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 0x0 := by rw [m17]; exact w16_74
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m17]; exact w16_428
  clear w16_74 w16_428 w16_64 w16_50 w16_38 w16_24 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_11 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  exact .inr ⟨hc1, hc2, hc3, n17, t17, s17, E17, V17, fR17, g17_2, g17_3, g17_4, g17_8, g17_9, g17_10, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, w17_24, w17_38, w17_50, w17_64, w17_74, w17_428, keep_kk17.mono (by decide)⟩

end C3.RV32.Sv
