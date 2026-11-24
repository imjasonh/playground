import C3BootProofs.Proofs.P2vEc

/-!
# `p256VerifyPrehash`: the signature's scalars and the key's tag

From 0x48 to 0x8E: the signature's `r` and `s` are in `[1, n)` for P-256's order `n`, and the key's SEC1 encoding starts with 4, an uncompressed point.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vA148 : List BInstr :=
  [.lui a2 0x3FCC4000, .aluImm .add a2 a2 0xF8, .aluImm .add a1 x0 0x20, .aluImm .add a3 x0 0x20, .alu .add a0 x0 (8 : Fin 32)]
theorem p2vA148_end : blockEnd p256VerifyPrehashCode 0x48 p2vA148 = some 0x5A := by
  simp only [p2vA148]
  rw [blockEnd, p2v_at_48]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_4c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_50]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_54]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_58]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA164 : List BInstr :=
  [.lui a2 0x3FCC4000, .aluImm .add a2 a2 0xF8, .aluImm .add a1 x0 0x20, .aluImm .add a3 x0 0x20, .alu .add a0 x0 (20 : Fin 32)]
theorem p2vA164_end : blockEnd p256VerifyPrehashCode 0x64 p2vA164 = some 0x76 := by
  simp only [p2vA164]
  rw [blockEnd, p2v_at_64]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_68]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_70]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_74]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA17e : List BInstr :=
  [.alu .add a1 x0 a0, .aluImm .add a0 x0 0x0]
theorem p2vA17e_end : blockEnd p256VerifyPrehashCode 0x7E p2vA17e = some 0x82 := by
  simp only [p2vA17e]
  rw [blockEnd, p2v_at_7e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_80]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA188 : List BInstr :=
  [.aluImm .add a2 x0 0x4]
theorem p2vA188_end : blockEnd p256VerifyPrehashCode 0x88 p2vA188 = some 0x8A := by
  simp only [p2vA188]
  rw [blockEnd, p2v_at_88]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_a1 {B pk dg rp sq : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0x48 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = rp)
    (g0_9 : reg n0 (9 : Fin 32) = pk)
    (g0_19 : reg n0 (19 : Fin 32) = dg)
    (g0_20 : reg n0 (20 : Fin 32) = sq)
    (r_in : P2vIn B rp 32)
    (s_in : P2vIn B sq 32)
    (k_in : P2vIn B pk 0x41)
    (dg_in : P2vIn B dg 32)
    (EC0 : P2vEcCode M0) :
    (¬ ((inScalarRange (memBytes M0 rp 32) (memBytes M0 (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true) ∧ (inScalarRange (memBytes M0 sq 32) (memBytes M0 (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true) ∧ (M0 pk = 4) ∧ True) ∧ P2vRet B v n0 0) ∨
    ((inScalarRange (memBytes M0 rp 32) (memBytes M0 (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true) ∧
    (inScalarRange (memBytes M0 sq 32) (memBytes M0 (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true) ∧
    (M0 pk = 4) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0x8E (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = rp ∧
        reg n' (9 : Fin 32) = pk ∧
        reg n' (19 : Fin 32) = dg ∧
        reg n' (20 : Fin 32) = sq ∧
        P2vKeepL B n0.mem n'.mem []) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x48
  obtain ⟨n1, c1, u1⟩ := s0.block p2vA148 E0.self p2vA148_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem P2V n1 0x5A (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock p2vA148 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
  have fr1 : ∀ x, P2vR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans c1
  have fR1 : ∀ x, P2vR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : P2vCode n1.mem := E0.fr F fr1
  have V1 : P2vSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by
    rw [rb1, runBlock_reg _ _ _ sp s0.zero (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb1, runBlock_reg _ _ _ (3 : Fin 32) s0.zero (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb1, runBlock_reg _ _ _ (4 : Fin 32) s0.zero (by decide), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = rp := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = pk := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
  have g1_19 : reg n1 (19 : Fin 32) = dg := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = sq := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_10 : reg n1 a0 = rp := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vA148, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_19, g0_20, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_11 : reg n1 a1 = BitVec.ofNat 32 0x20 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vA148, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_19, g0_20, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 (img% p256OrderBeAddress) := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vA148, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_19, g0_20, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_13 : reg n1 a3 = BitVec.ofNat 32 0x20 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vA148, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_19, g0_20, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  -- 0x5A: p2v_isrP
  obtain ⟨n2, c2, s2, rk2, a0_2, m2⟩ := p2v_isrP 
    E1 (EC0.p2v F fR1) s1 p2v_at_5a p2v_at_5e (by decide) (by decide) g1_10 g1_11 g1_12 g1_13
  rw [p2v_mb fR1 r_in, mb_dataR F fR1 (by decide) (by decide)] at a0_2
  have fr2 : ∀ x, P2vR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, P2vR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : P2vCode n2.mem := E1.fr F fr2
  have V2 : P2vSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rk2 sp (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk2 (3 : Fin 32) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk2 (4 : Fin 32) (by decide), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = rp := by rw [rk2 (8 : Fin 32) (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = pk := by rw [rk2 (9 : Fin 32) (by decide), g1_9]
  have g2_19 : reg n2 (19 : Fin 32) = dg := by rw [rk2 (19 : Fin 32) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = sq := by rw [rk2 (20 : Fin 32) (by decide), g1_20]
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  clear g1_13 g1_12 g1_11 g1_10 g1_20 g1_19 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  by_cases hr : inScalarRange (memBytes M0 rp 32) (memBytes M0 (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true
  rotate_left
  · have g2_10 : reg n2 a0 = BitVec.ofNat 32 0 := by rw [a0_2, ite_eq_right hr]; rfl
    -- 0x62: branch, taken
    obtain ⟨n3, d3, u3⟩ := s2.taken E2.self 0x144 p2v_at_62
      (by decide) (by rw [g2_10, s2.zero]; decide)
    have s3 : St n3.mem P2V n3 0x144 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, P2vR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : P2vCode n3.mem := E2.fr F fr3
    have V3 : P2vSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
    have g3_8 : reg n3 (8 : Fin 32) = rp := by rw [u3.regs, g2_8]
    have g3_9 : reg n3 (9 : Fin 32) = pk := by rw [u3.regs, g2_9]
    have g3_10 : reg n3 a0 = BitVec.ofNat 32 0x0 := by rw [u3.regs, g2_10]
    have g3_19 : reg n3 (19 : Fin 32) = dg := by rw [u3.regs, g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = sq := by rw [u3.regs, g2_20]
    have keep_kk3 : P2vKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    clear g2_20 g2_19 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 a0_2 rk2 s2 c2
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hr h0'), p2v_fail0 F E3 s3 t3 (fun x hx => (fR3 x hx).trans (fM x hx).symm) V3 hret g3_2 g3_3 g3_4 g3_10⟩
  have g2_10 : reg n2 a0 = BitVec.ofNat 32 1 := by rw [a0_2, ite_eq_left hr]; rfl
  -- 0x62: branch, not taken
  obtain ⟨n3, d3, u3⟩ := s2.notTaken E2.self 0x64 p2v_at_62
    (by decide) (by rw [g2_10, s2.zero]; decide)
  have s3 : St n3.mem P2V n3 0x64 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, P2vR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : P2vCode n3.mem := E2.fr F fr3
  have V3 : P2vSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = rp := by rw [u3.regs, g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = pk := by rw [u3.regs, g2_9]
  have g3_10 : reg n3 a0 = BitVec.ofNat 32 0x1 := by rw [u3.regs, g2_10]
  have g3_19 : reg n3 (19 : Fin 32) = dg := by rw [u3.regs, g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = sq := by rw [u3.regs, g2_20]
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  clear g2_20 g2_19 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 a0_2 rk2 s2 c2
  -- 0x64
  obtain ⟨n4, c4, u4⟩ := s3.block p2vA164 E3.self p2vA164_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem P2V n4 0x76 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock p2vA164 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  have fr4 : ∀ x, P2vR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans c4
  have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : P2vCode n4.mem := E3.fr F fr4
  have V4 : P2vSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by
    rw [rb4, runBlock_reg _ _ _ sp s3.zero (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb4, runBlock_reg _ _ _ (3 : Fin 32) s3.zero (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb4, runBlock_reg _ _ _ (4 : Fin 32) s3.zero (by decide), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = rp := by
    rw [rb4, runBlock_reg _ _ _ (8 : Fin 32) s3.zero (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = pk := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
  have g4_19 : reg n4 (19 : Fin 32) = dg := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = sq := by
    rw [rb4, runBlock_reg _ _ _ (20 : Fin 32) s3.zero (by decide), g3_20]
  have g4_10 : reg n4 a0 = sq := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vA164, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_19, g3_20, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g4_11 : reg n4 a1 = BitVec.ofNat 32 0x20 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vA164, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_19, g3_20, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g4_12 : reg n4 a2 = BitVec.ofNat 32 (img% p256OrderBeAddress) := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vA164, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_19, g3_20, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g4_13 : reg n4 a3 = BitVec.ofNat 32 0x20 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vA164, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_19, g3_20, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  clear g3_20 g3_19 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3 g2_10
  -- 0x76: p2v_isrP
  obtain ⟨n5, c5, s5, rk5, a0_5, m5⟩ := p2v_isrP 
    E4 (EC0.p2v F fR4) s4 p2v_at_76 p2v_at_7a (by decide) (by decide) g4_10 g4_11 g4_12 g4_13
  rw [p2v_mb fR4 s_in, mb_dataR F fR4 (by decide) (by decide)] at a0_5
  have fr5 : ∀ x, P2vR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, P2vR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : P2vCode n5.mem := E4.fr F fr5
  have V5 : P2vSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rk5 sp (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk5 (3 : Fin 32) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk5 (4 : Fin 32) (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = rp := by rw [rk5 (8 : Fin 32) (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = pk := by rw [rk5 (9 : Fin 32) (by decide), g4_9]
  have g5_19 : reg n5 (19 : Fin 32) = dg := by rw [rk5 (19 : Fin 32) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = sq := by rw [rk5 (20 : Fin 32) (by decide), g4_20]
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  clear g4_13 g4_12 g4_11 g4_10 g4_20 g4_19 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  by_cases hs : inScalarRange (memBytes M0 sq 32) (memBytes M0 (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true
  rotate_left
  · have g5_10 : reg n5 a0 = BitVec.ofNat 32 0 := by rw [a0_5, ite_eq_right hs]; rfl
    -- 0x7E
    obtain ⟨n6, c6, u6⟩ := s5.block p2vA17e E5.self p2vA17e_end
      ⟨trivial, trivial, trivial⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have s6 : St n6.mem P2V n6 0x82 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have rb6 : ∀ q, reg n6 q = (runBlock p2vA17e (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
    have fr6 : ∀ x, P2vR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
    have t6 : Steps n0 n6 := t5.trans c6
    have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
    have E6 : P2vCode n6.mem := E5.fr F fr6
    have V6 : P2vSaves B n6.mem v := V5.same m6
    have g6_2 : reg n6 sp = B + 0x21A0 := by
      rw [rb6, runBlock_reg _ _ _ sp s5.zero (by decide), g5_2]
    have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb6, runBlock_reg _ _ _ (3 : Fin 32) s5.zero (by decide), g5_3]
    have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb6, runBlock_reg _ _ _ (4 : Fin 32) s5.zero (by decide), g5_4]
    have g6_8 : reg n6 (8 : Fin 32) = rp := by
      rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
    have g6_9 : reg n6 (9 : Fin 32) = pk := by
      rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
    have g6_19 : reg n6 (19 : Fin 32) = dg := by
      rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
    have g6_20 : reg n6 (20 : Fin 32) = sq := by
      rw [rb6, runBlock_reg _ _ _ (20 : Fin 32) s5.zero (by decide), g5_20]
    have g6_10 : reg n6 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb6]; simp +decide only [runBlock, BInstr.run, p2vA17e, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_19, g5_20, s5.zero])
      all_goals first | with_reducible rfl | p2v_addr | decide
    have g6_11 : reg n6 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb6]; simp +decide only [runBlock, BInstr.run, p2vA17e, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_19, g5_20, s5.zero])
      all_goals first | with_reducible rfl | p2v_addr | decide
    have keep_kk6 : P2vKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    clear g5_20 g5_19 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 a0_5 rk5 s5 c5
    -- 0x82: branch, taken
    obtain ⟨n7, d7, u7⟩ := s6.taken E6.self 0x144 p2v_at_82
      (by decide) (by rw [g6_11, s6.zero]; decide)
    have s7 : St n7.mem P2V n7 0x144 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, P2vR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : P2vCode n7.mem := E6.fr F fr7
    have V7 : P2vSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
    have g7_8 : reg n7 (8 : Fin 32) = rp := by rw [u7.regs, g6_8]
    have g7_9 : reg n7 (9 : Fin 32) = pk := by rw [u7.regs, g6_9]
    have g7_10 : reg n7 a0 = BitVec.ofNat 32 0x0 := by rw [u7.regs, g6_10]
    have g7_11 : reg n7 a1 = BitVec.ofNat 32 0x0 := by rw [u7.regs, g6_11]
    have g7_19 : reg n7 (19 : Fin 32) = dg := by rw [u7.regs, g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = sq := by rw [u7.regs, g6_20]
    have keep_kk7 : P2vKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    clear g6_11 g6_10 g6_20 g6_19 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6 g5_10
    exact .inl ⟨(fun ⟨h0', h1', _⟩ => by exact hs h1'), p2v_fail0 F E7 s7 t7 (fun x hx => (fR7 x hx).trans (fM x hx).symm) V7 hret g7_2 g7_3 g7_4 g7_10⟩
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 1 := by rw [a0_5, ite_eq_left hs]; rfl
  -- 0x7E
  obtain ⟨n6, c6, u6⟩ := s5.block p2vA17e E5.self p2vA17e_end
    ⟨trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem P2V n6 0x82 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock p2vA17e (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have fr6 : ∀ x, P2vR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by
    rw [rb6, runBlock_reg _ _ _ sp s5.zero (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb6, runBlock_reg _ _ _ (3 : Fin 32) s5.zero (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb6, runBlock_reg _ _ _ (4 : Fin 32) s5.zero (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = rp := by
    rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = pk := by
    rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
  have g6_19 : reg n6 (19 : Fin 32) = dg := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = sq := by
    rw [rb6, runBlock_reg _ _ _ (20 : Fin 32) s5.zero (by decide), g5_20]
  have g6_10 : reg n6 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, p2vA17e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_19, g5_20, s5.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g6_11 : reg n6 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, p2vA17e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_19, g5_20, s5.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  clear g5_20 g5_19 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 a0_5 rk5 s5 c5
  -- 0x82: branch, not taken
  obtain ⟨n7, d7, u7⟩ := s6.notTaken E6.self 0x84 p2v_at_82
    (by decide) (by rw [g6_11, s6.zero]; decide)
  have s7 : St n7.mem P2V n7 0x84 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, P2vR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : P2vCode n7.mem := E6.fr F fr7
  have V7 : P2vSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = rp := by rw [u7.regs, g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = pk := by rw [u7.regs, g6_9]
  have g7_10 : reg n7 a0 = BitVec.ofNat 32 0x0 := by rw [u7.regs, g6_10]
  have g7_11 : reg n7 a1 = BitVec.ofNat 32 0x1 := by rw [u7.regs, g6_11]
  have g7_19 : reg n7 (19 : Fin 32) = dg := by rw [u7.regs, g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = sq := by rw [u7.regs, g6_20]
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  clear g6_11 g6_10 g6_20 g6_19 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6 g5_10
  -- 0x84: lbu from the bundle
  obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self p2v_at_84 (off' := 0x88) (by decide)
  have s8 : St n8.mem P2V n8 0x88 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, P2vR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, P2vR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : P2vCode n8.mem := E7.fr F fr8
  have V8 : P2vSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = rp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = pk := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
  have g8_10 : reg n8 a0 = BitVec.ofNat 32 0x0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_10]
  have g8_19 : reg n8 (19 : Fin 32) = dg := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = sq := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
  have g8_11 : reg n8 a1 = (M0 (pk)).zeroExtend 32 := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_9, show (pk) + 0x0 = pk from BitVec.add_zero _, fR7 _ (k_in.r0 (by decide))]
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  clear g7_20 g7_19 g7_11 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x88
  obtain ⟨n9, c9, u9⟩ := s8.block p2vA188 E8.self p2vA188_end
    ⟨trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem P2V n9 0x8A (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock p2vA188 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  have fr9 : ∀ x, P2vR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, P2vR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : P2vCode n9.mem := E8.fr F fr9
  have V9 : P2vSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by
    rw [rb9, runBlock_reg _ _ _ sp s8.zero (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (3 : Fin 32) s8.zero (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (4 : Fin 32) s8.zero (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = rp := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = pk := by
    rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
  have g9_10 : reg n9 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb9, runBlock_reg _ _ _ a0 s8.zero (by decide), g8_10]
  have g9_11 : reg n9 a1 = (M0 (pk)).zeroExtend 32 := by
    rw [rb9, runBlock_reg _ _ _ a1 s8.zero (by decide), g8_11]
  have g9_19 : reg n9 (19 : Fin 32) = dg := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = sq := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_12 : reg n9 a2 = BitVec.ofNat 32 0x4 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vA188, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_19, g8_20, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  clear g8_11 g8_20 g8_19 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  by_cases htag : M0 pk = 4
  rotate_left
  · -- 0x8A: branch, taken
    obtain ⟨n10, d10, u10⟩ := s9.taken E9.self 0x144 p2v_at_8a
      (by decide) (by rw [g9_11, g9_12]; exact br_bne_t fun e => htag ((zext_eq4 _).mp e))
    have s10 : St n10.mem P2V n10 0x144 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, P2vR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : P2vCode n10.mem := E9.fr F fr10
    have V10 : P2vSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = rp := by rw [u10.regs, g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = pk := by rw [u10.regs, g9_9]
    have g10_10 : reg n10 a0 = BitVec.ofNat 32 0x0 := by rw [u10.regs, g9_10]
    have g10_11 : reg n10 a1 = (M0 (pk)).zeroExtend 32 := by rw [u10.regs, g9_11]
    have g10_12 : reg n10 a2 = BitVec.ofNat 32 0x4 := by rw [u10.regs, g9_12]
    have g10_19 : reg n10 (19 : Fin 32) = dg := by rw [u10.regs, g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = sq := by rw [u10.regs, g9_20]
    have keep_kk10 : P2vKeepL B n0.mem n10.mem [] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    clear g9_12 g9_20 g9_19 g9_11 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
    exact .inl ⟨(fun ⟨h0', h1', h2', _⟩ => by exact htag h2'), p2v_fail0 F E10 s10 t10 (fun x hx => (fR10 x hx).trans (fM x hx).symm) V10 hret g10_2 g10_3 g10_4 g10_10⟩
  -- 0x8A: branch, not taken
  obtain ⟨n10, d10, u10⟩ := s9.notTaken E9.self 0x8E p2v_at_8a
    (by decide) (by rw [g9_11, g9_12, htag]; decide)
  have s10 : St n10.mem P2V n10 0x8E (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, P2vR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : P2vCode n10.mem := E9.fr F fr10
  have V10 : P2vSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = rp := by rw [u10.regs, g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = pk := by rw [u10.regs, g9_9]
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 0x0 := by rw [u10.regs, g9_10]
  have g10_11 : reg n10 a1 = (M0 (pk)).zeroExtend 32 := by rw [u10.regs, g9_11]
  have g10_12 : reg n10 a2 = BitVec.ofNat 32 0x4 := by rw [u10.regs, g9_12]
  have g10_19 : reg n10 (19 : Fin 32) = dg := by rw [u10.regs, g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = sq := by rw [u10.regs, g9_20]
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  clear g9_12 g9_20 g9_19 g9_11 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  exact .inr ⟨hr, hs, htag, n10, t10, s10, E10, V10, fR10, g10_2, g10_3, g10_4, g10_8, g10_9, g10_19, g10_20, keep_kk10.mono (by decide)⟩

end C3.RV32.P2v
