import C3BootProofs.Proofs.P2vEc

/-!
# `p256VerifyPrehash`: the key's point and the signature's scalars

From 0x8E to 0x186: the key decodes to a point on P-256, and the signature's `r` and `s` are scalars below the order and not zero.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vA28e : List BInstr :=
  [.aluImm .add a0 sp 0x98, .alu .add a1 x0 (9 : Fin 32)]
theorem p2vA28e_end : blockEnd p256VerifyPrehashCode 0x8E p2vA28e = some 0x92 := by
  simp only [p2vA28e]
  rw [blockEnd, p2v_at_8e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_90]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA29e : List BInstr :=
  [.aluImm .add (26 : Fin 32) sp 0x7FF, .aluImm .add (26 : Fin 32) (26 : Fin 32) 0x121, .aluImm .add a1 sp 0x9C, .aluImm .add a0 sp 0x58, .aluImm .add a2 x0 0x40]
theorem p2vA29e_end : blockEnd p256VerifyPrehashCode 0x9E p2vA29e = some 0xAE := by
  simp only [p2vA29e]
  rw [blockEnd, p2v_at_9e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_a2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_a6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_a8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_aa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA2ba : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .alu .add a1 x0 (8 : Fin 32)]
theorem p2vA2ba_end : blockEnd p256VerifyPrehashCode 0xBA p2vA2ba = some 0xC4 := by
  simp only [p2vA2ba]
  rw [blockEnd, p2v_at_ba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_be]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_c2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA2d2 : List BInstr :=
  [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x485, .aluImm .add a0 sp 0x200, .aluImm .add a2 x0 0x20]
theorem p2vA2d2_end : blockEnd p256VerifyPrehashCode 0xD2 p2vA2d2 = some 0xE0 := by
  simp only [p2vA2d2]
  rw [blockEnd, p2v_at_d2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_d6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_da]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_dc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA2e8 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .alu .add a1 x0 (20 : Fin 32)]
theorem p2vA2e8_end : blockEnd p256VerifyPrehashCode 0xE8 p2vA2e8 = some 0xF2 := by
  simp only [p2vA2e8]
  rw [blockEnd, p2v_at_e8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA2100 : List BInstr :=
  [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x485, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x7E5, .aluImm .add a2 x0 0x20]
theorem p2vA2100_end : blockEnd p256VerifyPrehashCode 0x100 p2vA2100 = some 0x114 := by
  simp only [p2vA2100]
  rw [blockEnd, p2v_at_100]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_104]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_108]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_10c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_110]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA211c : List BInstr :=
  [.aluImm .add a0 sp 0x200]
theorem p2vA211c_end : blockEnd p256VerifyPrehashCode 0x11C p2vA211c = some 0x11E := by
  simp only [p2vA211c]
  rw [blockEnd, p2v_at_11c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA2126 : List BInstr :=
  [.aluImm .and a0 a0 0xFF]
theorem p2vA2126_end : blockEnd p256VerifyPrehashCode 0x126 p2vA2126 = some 0x12A := by
  simp only [p2vA2126]
  rw [blockEnd, p2v_at_126]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA212c : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x7E5]
theorem p2vA212c_end : blockEnd p256VerifyPrehashCode 0x12C p2vA212c = some 0x134 := by
  simp only [p2vA212c]
  rw [blockEnd, p2v_at_12c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_130]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA213c : List BInstr :=
  [.aluImm .and a0 a0 0xFF]
theorem p2vA213c_end : blockEnd p256VerifyPrehashCode 0x13C p2vA213c = some 0x140 := by
  simp only [p2vA213c]
  rw [blockEnd, p2v_at_13c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_a2 {B pk dg rp sq : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0x8E (reg n0))
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
    (EC0 : P2vEcCode M0)
    (D0 : P2Data M0)
    (BG0 : BGEnv M0) :
    (¬ ((GsOk M0 pk) ∧ (beNat (memBytes M0 rp 32) < C3.p256.n) ∧ (beNat (memBytes M0 sq 32) < C3.p256.n) ∧ (beNat (memBytes M0 rp 32) ≠ 0) ∧ (beNat (memBytes M0 sq 32) ≠ 0) ∧ True) ∧ P2vRet B v n0 0) ∨
    ((GsOk M0 pk) ∧
    (beNat (memBytes M0 rp 32) < C3.p256.n) ∧
    (beNat (memBytes M0 sq 32) < C3.p256.n) ∧
    (beNat (memBytes M0 rp 32) ≠ 0) ∧
    (beNat (memBytes M0 sq 32) ≠ 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0x186 (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 ∧
        reg n' (19 : Fin 32) = dg ∧
        reg n' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) ∧
        P2vKeepL B n0.mem n'.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x8E
  obtain ⟨n1, c1, u1⟩ := s0.block p2vA28e E0.self p2vA28e_end
    ⟨trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem P2V n1 0x92 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock p2vA28e (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x98 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vA28e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_19, g0_20, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_11 : reg n1 a1 = pk := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vA28e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_19, g0_20, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  -- 0x92: p2v_gsFull
  obtain ⟨n2, c2, s2, sp2, rk2, K2, Ok2, Er2, fr2⟩ := p2v_gsFull (oc := 0x98)
    F E1 (P2Data.p2v F D0 fR1) s1 p2v_at_92 p2v_at_96 (by decide) (by decide) g1_2
    g1_10 g1_11 (by decide) (by decide) k_in
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, P2vR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : P2vCode n2.mem := E1.fr F fr2
  have V2 : P2vSaves B n2.mem v := V1.keepL K2 (by decide)
  rw [gsOk_congr (p2v_pt fR1 k_in)] at Ok2 Er2
  rw [gsVal_sv fR1 k_in (o := 1) (by decide), gsVal_sv fR1 k_in (o := 0x21) (by decide)] at Ok2
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk2 (3 : Fin 32) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk2 (4 : Fin 32) (by decide), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = rp := by rw [rk2 (8 : Fin 32) (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = pk := by rw [rk2 (9 : Fin 32) (by decide), g1_9]
  have g2_19 : reg n2 (19 : Fin 32) = dg := by rw [rk2 (19 : Fin 32) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = sq := by rw [rk2 (20 : Fin 32) (by decide), g1_20]
  have g2_2 : reg n2 sp = B + 0x21A0 := sp2
  by_cases hgs : GsOk M0 pk
  rotate_left
  · have z2 := Er2 hgs
    have keep_kk2 : P2vKeepL B n0.mem n2.mem [(0x98, 0x48)] := keep_kk1.trans K2
    clear keep_kk1
    have w2_98 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 1 := z2
    clear g1_11 g1_10 g1_20 g1_19 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0x9A: lw
    obtain ⟨n3, d3, u3⟩ := s2.lw E2.self p2v_at_9a (off' := 0x9C) (by decide)
      (by rw [g2_2, show B + 0x21A0 + 0x98 = B + 0x21A0 + BitVec.ofNat 32 0x98 by p2v_addr]; exact p2v_al F (by decide) (by decide))
    have s3 : St n3.mem P2V n3 0x9C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, P2vR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : P2vCode n3.mem := E2.fr F fr3
    have V3 : P2vSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
    have g3_8 : reg n3 (8 : Fin 32) = rp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
    have g3_9 : reg n3 (9 : Fin 32) = pk := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
    have g3_19 : reg n3 (19 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = sq := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
    have g3_10 : reg n3 a0 = 1 := by
      rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g2_2, show B + 0x21A0 + 0x98 = B + 0x21A0 + BitVec.ofNat 32 0x98 by p2v_addr, w2_98]
    have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0x98, 0x48)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_98 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 1 := by rw [m3]; exact w2_98
    clear w2_98 z2
    -- 0x9C: branch, taken
    obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x142 p2v_at_9c
      (by decide) (by rw [g3_10, s3.zero]; decide)
    have s4 : St n4.mem P2V n4 0x142 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, P2vR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : P2vCode n4.mem := E3.fr F fr4
    have V4 : P2vSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
    have g4_8 : reg n4 (8 : Fin 32) = rp := by rw [u4.regs, g3_8]
    have g4_9 : reg n4 (9 : Fin 32) = pk := by rw [u4.regs, g3_9]
    have g4_10 : reg n4 a0 = 1 := by rw [u4.regs, g3_10]
    have g4_19 : reg n4 (19 : Fin 32) = dg := by rw [u4.regs, g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = sq := by rw [u4.regs, g3_20]
    have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0x98, 0x48)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_98 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 1 := by rw [m4]; exact w3_98
    clear w3_98 g3_10 g3_20 g3_19 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hgs h0'), p2v_fail F E4 s4 t4 (fun x hx => (fR4 x hx).trans (fM x hx).symm) V4 hret g4_2 g4_3 g4_4⟩
  obtain ⟨o1_2, o2_2, o3_2, o4_2⟩ := Ok2 hgs
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [(0x98, 0x48)] := keep_kk1.trans K2
  clear keep_kk1
  have a2_9c : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := o2_2
  have a2_bc : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := o3_2
  have w2_98 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := o1_2
  have b2_dc : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := o4_2
  clear g1_11 g1_10 g1_20 g1_19 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x9A: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self p2v_at_9a (off' := 0x9C) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x98 = B + 0x21A0 + BitVec.ofNat 32 0x98 by p2v_addr]; exact p2v_al F (by decide) (by decide))
  have s3 : St n3.mem P2V n3 0x9C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, P2vR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : P2vCode n3.mem := E2.fr F fr3
  have V3 : P2vSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = rp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = pk := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_19 : reg n3 (19 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = sq := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_10 : reg n3 a0 = 0 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x98 = B + 0x21A0 + BitVec.ofNat 32 0x98 by p2v_addr, w2_98]
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0x98, 0x48)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_98 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m3]; exact w2_98
  have b3_dc : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m3]; exact b2_dc
  have a3_9c : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m3]; exact a2_9c
  have a3_bc : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m3]; exact a2_bc
  clear b2_dc w2_98 a2_bc a2_9c o4_2 o3_2 o2_2 o1_2 g2_2 g2_20 g2_19 g2_9 g2_8 g2_4 g2_3 V2 E2 fR2 t2 fr2 Er2 Ok2 K2 rk2 sp2 s2 c2
  -- 0x9C: branch, not taken
  obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0x9E p2v_at_9c
    (by decide) (by rw [g3_10, s3.zero]; decide)
  have s4 : St n4.mem P2V n4 0x9E (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, P2vR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : P2vCode n4.mem := E3.fr F fr4
  have V4 : P2vSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = rp := by rw [u4.regs, g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = pk := by rw [u4.regs, g3_9]
  have g4_10 : reg n4 a0 = 0 := by rw [u4.regs, g3_10]
  have g4_19 : reg n4 (19 : Fin 32) = dg := by rw [u4.regs, g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = sq := by rw [u4.regs, g3_20]
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0x98, 0x48)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_98 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m4]; exact w3_98
  have b4_dc : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m4]; exact b3_dc
  have a4_9c : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m4]; exact a3_9c
  have a4_bc : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m4]; exact a3_bc
  clear a3_bc a3_9c b3_dc w3_98 g3_10 g3_20 g3_19 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x9E
  obtain ⟨n5, c5, u5⟩ := s4.block p2vA29e E4.self p2vA29e_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem P2V n5 0xAE (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock p2vA29e (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have fr5 : ∀ x, P2vR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, P2vR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : P2vCode n5.mem := E4.fr F fr5
  have V5 : P2vSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by
    rw [rb5, runBlock_reg _ _ _ sp s4.zero (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (3 : Fin 32) s4.zero (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (4 : Fin 32) s4.zero (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = rp := by
    rw [rb5, runBlock_reg _ _ _ (8 : Fin 32) s4.zero (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = pk := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_19 : reg n5 (19 : Fin 32) = dg := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = sq := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x58 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vA29e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_10, g4_19, g4_20, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g5_11 : reg n5 a1 = B + 0x21A0 + BitVec.ofNat 32 0x9C := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vA29e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_10, g4_19, g4_20, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g5_12 : reg n5 a2 = BitVec.ofNat 32 0x40 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vA29e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_10, g4_19, g4_20, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g5_26 : reg n5 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vA29e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_10, g4_19, g4_20, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0x98, 0x48)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_98 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m5]; exact w4_98
  have b5_dc : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m5]; exact b4_dc
  have a5_9c : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m5]; exact a4_9c
  have a5_bc : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m5]; exact a4_bc
  clear a4_bc a4_9c b4_dc w4_98 g4_20 g4_19 g4_10 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0xAE: memcpy
  obtain ⟨n6, P6, K6, X6⟩ := p2v_mc (c := 0x58) (d := 0x9C) (N := 0x40) F E5 s5 p2v_at_ae p2v_at_b2
    (by decide) (by decide) g5_2 g5_10 g5_11 g5_12
    (by decide) (by decide) (by decide)
  have s6 := P6.st
  have fr6 := P6.fr
  have t6 : Steps n0 n6 := t5.trans P6.steps
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [P6.regs sp (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P6.regs (3 : Fin 32) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P6.regs (4 : Fin 32) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = rp := by rw [P6.regs (8 : Fin 32) (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = pk := by rw [P6.regs (9 : Fin 32) (by decide), g5_9]
  have g6_19 : reg n6 (19 : Fin 32) = dg := by rw [P6.regs (19 : Fin 32) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = sq := by rw [P6.regs (20 : Fin 32) (by decide), g5_20]
  have g6_26 : reg n6 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P6.regs (26 : Fin 32) (by decide), g5_26]
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0x98, 0x48), (0x58, 0x40)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_98 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := (K6.w32 (by decide) (by decide)).trans w5_98
  have b6_dc : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := (K6.b8 (by decide) (by decide)).trans b5_dc
  have a6_9c : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K6.acc (by decide) (by decide)).trans a5_9c
  have a6_bc : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K6.acc (by decide) (by decide)).trans a5_bc
  have a6_58 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (accV_S 8 fun q hq => by
    rw [show 0x58 + q = 0x58 + (0x0 + q) by omega, X6 (0x0 + q) (by omega),
      show 0x9C + (0x0 + q) = 0x9C + q by omega]).trans a5_9c
  have a6_78 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (accV_S 8 fun q hq => by
    rw [show 0x78 + q = 0x58 + (0x20 + q) by omega, X6 (0x20 + q) (by omega),
      show 0x9C + (0x20 + q) = 0xBC + q by omega]).trans a5_bc
  clear a5_bc a5_9c b5_dc w5_98 g5_26 g5_12 g5_11 g5_10 g5_20 g5_19 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0xB6: lbu
  obtain ⟨n7, d7, u7⟩ := s6.lbu E6.self p2v_at_b6 (off' := 0xBA) (by decide)
  have s7 : St n7.mem P2V n7 0xBA (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, P2vR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : P2vCode n7.mem := E6.fr F fr7
  have V7 : P2vSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = rp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = pk := by rw [u7.regs, upd_ne (by decide) (by decide), g6_9]
  have g7_19 : reg n7 (19 : Fin 32) = dg := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = sq := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
  have g7_26 : reg n7 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_18 : reg n7 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0xDC = B + 0x21A0 + BitVec.ofNat 32 0xDC by p2v_addr, b6_dc]
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0x98, 0x48), (0x58, 0x40)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_98 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m7]; exact w6_98
  have b7_dc : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m7]; exact b6_dc
  have a7_58 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m7]; exact a6_58
  have a7_78 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m7]; exact a6_78
  have a7_9c : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m7]; exact a6_9c
  have a7_bc : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m7]; exact a6_bc
  clear a6_78 a6_58 a6_bc a6_9c b6_dc w6_98 g6_26 g6_20 g6_19 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 s6 X6 K6 P6
  -- 0xBA
  obtain ⟨n8, c8, u8⟩ := s7.block p2vA2ba E7.self p2vA2ba_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem P2V n8 0xC4 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock p2vA2ba (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  have fr8 : ∀ x, P2vR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, P2vR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : P2vCode n8.mem := E7.fr F fr8
  have V8 : P2vSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by
    rw [rb8, runBlock_reg _ _ _ sp s7.zero (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb8, runBlock_reg _ _ _ (3 : Fin 32) s7.zero (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb8, runBlock_reg _ _ _ (4 : Fin 32) s7.zero (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = rp := by
    rw [rb8, runBlock_reg _ _ _ (8 : Fin 32) s7.zero (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = pk := by
    rw [rb8, runBlock_reg _ _ _ (9 : Fin 32) s7.zero (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = dg := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = sq := by
    rw [rb8, runBlock_reg _ _ _ (20 : Fin 32) s7.zero (by decide), g7_20]
  have g8_26 : reg n8 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vA2ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_18, g7_19, g7_20, g7_26, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g8_11 : reg n8 a1 = rp := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vA2ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_18, g7_19, g7_20, g7_26, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0x98, 0x48), (0x58, 0x40)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_98 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m8]; exact w7_98
  have b8_dc : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m8]; exact b7_dc
  have a8_58 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m8]; exact a7_58
  have a8_78 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m8]; exact a7_78
  have a8_9c : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m8]; exact a7_9c
  have a8_bc : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m8]; exact a7_bc
  clear a7_bc a7_9c a7_78 a7_58 b7_dc w7_98 g7_18 g7_26 g7_20 g7_19 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0xC4: p2v_sf2P
  obtain ⟨n9, c9, s9, sp9, rk9, L9, G9, K9, fr9⟩ := p2v_sf2P (co := 0xC80)
    F E8 (BG0.p2v F fR8) s8 p2v_at_c4 p2v_at_c8 (by decide) (by decide) g8_2
    g8_10 g8_11 (by decide) (by decide) r_in
  rw [p2v_mb fR8 r_in] at L9 G9
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, P2vR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : P2vCode n9.mem := E8.fr F fr9
  have V9 : P2vSaves B n9.mem v := V8.keepL K9 (by decide)
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk9 (3 : Fin 32) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk9 (4 : Fin 32) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = rp := by rw [rk9 (8 : Fin 32) (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = pk := by rw [rk9 (9 : Fin 32) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk9 (18 : Fin 32) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = dg := by rw [rk9 (19 : Fin 32) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = sq := by rw [rk9 (20 : Fin 32) (by decide), g8_20]
  have g9_26 : reg n9 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk9 (26 : Fin 32) (by decide), g8_26]
  have g9_2 : reg n9 sp = B + 0x21A0 := sp9
  by_cases hlr : beNat (memBytes M0 rp 32) < C3.p256.n
  rotate_left
  · have z9 := G9 (Nat.le_of_not_lt hlr)
    have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24)] := keep_kk8.trans K9
    clear keep_kk8
    have w9_98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := (K9.w32 (by decide) (by decide)).trans w8_98
    have b9_dc : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := (K9.b8 (by decide) (by decide)).trans b8_dc
    have a9_58 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K9.acc (by decide) (by decide)).trans a8_58
    have a9_78 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K9.acc (by decide) (by decide)).trans a8_78
    have a9_9c : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K9.acc (by decide) (by decide)).trans a8_9c
    have a9_bc : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K9.acc (by decide) (by decide)).trans a8_bc
    have w9_c80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 1 := z9
    clear a8_bc a8_9c a8_78 a8_58 b8_dc w8_98 g8_11 g8_10 g8_26 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
    -- 0xCC: lw
    obtain ⟨n10, d10, u10⟩ := s9.lw E9.self p2v_at_cc (off' := 0xD0) (by decide)
      (by rw [g9_26, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x360 = B + 0x21A0 + BitVec.ofNat 32 0xC80 by p2v_addr]; exact p2v_al F (by decide) (by decide))
    have s10 : St n10.mem P2V n10 0xD0 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, P2vR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : P2vCode n10.mem := E9.fr F fr10
    have V10 : P2vSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = rp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = pk := by rw [u10.regs, upd_ne (by decide) (by decide), g9_9]
    have g10_18 : reg n10 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = dg := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = sq := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
    have g10_26 : reg n10 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
    have g10_10 : reg n10 a0 = 1 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g9_26, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x360 = B + 0x21A0 + BitVec.ofNat 32 0xC80 by p2v_addr, w9_c80]
    have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m10]; exact w9_98
    have w10_c80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 1 := by rw [m10]; exact w9_c80
    have b10_dc : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m10]; exact b9_dc
    have a10_58 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m10]; exact a9_58
    have a10_78 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m10]; exact a9_78
    have a10_9c : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m10]; exact a9_9c
    have a10_bc : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m10]; exact a9_bc
    clear w9_c80 a9_bc a9_9c a9_78 a9_58 b9_dc w9_98 z9
    -- 0xD0: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x142 p2v_at_d0
      (by decide) (by rw [g10_10, s10.zero]; decide)
    have s11 : St n11.mem P2V n11 0x142 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, P2vR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : P2vCode n11.mem := E10.fr F fr11
    have V11 : P2vSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = rp := by rw [u11.regs, g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = pk := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = 1 := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = dg := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = sq := by rw [u11.regs, g10_20]
    have g11_26 : reg n11 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u11.regs, g10_26]
    have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m11]; exact w10_98
    have w11_c80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 1 := by rw [m11]; exact w10_c80
    have b11_dc : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m11]; exact b10_dc
    have a11_58 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m11]; exact a10_58
    have a11_78 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m11]; exact a10_78
    have a11_9c : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m11]; exact a10_9c
    have a11_bc : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m11]; exact a10_bc
    clear a10_bc a10_9c a10_78 a10_58 b10_dc w10_c80 w10_98 g10_10 g10_26 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    exact .inl ⟨(fun ⟨h0', h1', _⟩ => by exact hlr h1'), p2v_fail F E11 s11 t11 (fun x hx => (fR11 x hx).trans (fM x hx).symm) V11 hret g11_2 g11_3 g11_4⟩
  obtain ⟨z9, y9⟩ := L9 hlr
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24)] := keep_kk8.trans K9
  clear keep_kk8
  have w9_98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := (K9.w32 (by decide) (by decide)).trans w8_98
  have b9_dc : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := (K9.b8 (by decide) (by decide)).trans b8_dc
  have a9_58 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K9.acc (by decide) (by decide)).trans a8_58
  have a9_78 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K9.acc (by decide) (by decide)).trans a8_78
  have a9_9c : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K9.acc (by decide) (by decide)).trans a8_9c
  have a9_bc : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K9.acc (by decide) (by decide)).trans a8_bc
  have a9_c84 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 rp 32) := by rw [show B + 0x21A0 + BitVec.ofNat 32 0xC84 = B + 0x21A0 + BitVec.ofNat 32 0xC80 + 4 by p2v_addr]; exact y9
  have w9_c80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := z9
  clear a8_bc a8_9c a8_78 a8_58 b8_dc w8_98 g8_11 g8_10 g8_26 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0xCC: lw
  obtain ⟨n10, d10, u10⟩ := s9.lw E9.self p2v_at_cc (off' := 0xD0) (by decide)
    (by rw [g9_26, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x360 = B + 0x21A0 + BitVec.ofNat 32 0xC80 by p2v_addr]; exact p2v_al F (by decide) (by decide))
  have s10 : St n10.mem P2V n10 0xD0 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, P2vR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : P2vCode n10.mem := E9.fr F fr10
  have V10 : P2vSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = rp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = pk := by rw [u10.regs, upd_ne (by decide) (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = dg := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = sq := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
  have g10_26 : reg n10 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
  have g10_10 : reg n10 a0 = 0 := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_26, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x360 = B + 0x21A0 + BitVec.ofNat 32 0xC80 by p2v_addr, w9_c80]
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m10]; exact w9_98
  have w10_c80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m10]; exact w9_c80
  have b10_dc : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m10]; exact b9_dc
  have a10_58 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m10]; exact a9_58
  have a10_78 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m10]; exact a9_78
  have a10_9c : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m10]; exact a9_9c
  have a10_bc : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m10]; exact a9_bc
  have a10_c84 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 rp 32) := by rw [m10]; exact a9_c84
  clear w9_c80 a9_c84 a9_bc a9_9c a9_78 a9_58 b9_dc w9_98 y9 z9 g9_2 g9_26 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 V9 E9 fR9 t9 fr9 K9 G9 L9 rk9 sp9 s9 c9
  -- 0xD0: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0xD2 p2v_at_d0
    (by decide) (by rw [g10_10, s10.zero]; decide)
  have s11 : St n11.mem P2V n11 0xD2 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, P2vR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : P2vCode n11.mem := E10.fr F fr11
  have V11 : P2vSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = rp := by rw [u11.regs, g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = pk := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = 0 := by rw [u11.regs, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = dg := by rw [u11.regs, g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = sq := by rw [u11.regs, g10_20]
  have g11_26 : reg n11 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u11.regs, g10_26]
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m11]; exact w10_98
  have w11_c80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m11]; exact w10_c80
  have b11_dc : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m11]; exact b10_dc
  have a11_58 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m11]; exact a10_58
  have a11_78 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m11]; exact a10_78
  have a11_9c : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m11]; exact a10_9c
  have a11_bc : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m11]; exact a10_bc
  have a11_c84 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 rp 32) := by rw [m11]; exact a10_c84
  clear a10_c84 a10_bc a10_9c a10_78 a10_58 b10_dc w10_c80 w10_98 g10_10 g10_26 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0xD2
  obtain ⟨n12, c12, u12⟩ := s11.block p2vA2d2 E11.self p2vA2d2_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem P2V n12 0xE0 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock p2vA2d2 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
  have fr12 : ∀ x, P2vR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans c12
  have fR12 : ∀ x, P2vR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : P2vCode n12.mem := E11.fr F fr12
  have V12 : P2vSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by
    rw [rb12, runBlock_reg _ _ _ sp s11.zero (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (3 : Fin 32) s11.zero (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (4 : Fin 32) s11.zero (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = rp := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = pk := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = dg := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = sq := by
    rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
  have g12_26 : reg n12 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vA2d2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_26, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vA2d2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_26, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g12_12 : reg n12 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vA2d2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_26, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_98 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m12]; exact w11_98
  have w12_c80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m12]; exact w11_c80
  have b12_dc : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m12]; exact b11_dc
  have a12_58 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m12]; exact a11_58
  have a12_78 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m12]; exact a11_78
  have a12_9c : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m12]; exact a11_9c
  have a12_bc : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m12]; exact a11_bc
  have a12_c84 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 rp 32) := by rw [m12]; exact a11_c84
  clear a11_c84 a11_bc a11_9c a11_78 a11_58 b11_dc w11_c80 w11_98 g11_26 g11_20 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0xE0: memcpy
  obtain ⟨n13, P13, K13, X13⟩ := p2v_mc (c := 0x200) (d := 0xC84) (N := 0x20) F E12 s12 p2v_at_e0 p2v_at_e4
    (by decide) (by decide) g12_2 g12_10 g12_11 g12_12
    (by decide) (by decide) (by decide)
  have s13 := P13.st
  have fr13 := P13.fr
  have t13 : Steps n0 n13 := t12.trans P13.steps
  have fR13 : ∀ x, P2vR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : P2vCode n13.mem := E12.fr F fr13
  have V13 : P2vSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [P13.regs sp (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P13.regs (3 : Fin 32) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P13.regs (4 : Fin 32) (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = rp := by rw [P13.regs (8 : Fin 32) (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = pk := by rw [P13.regs (9 : Fin 32) (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P13.regs (18 : Fin 32) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = dg := by rw [P13.regs (19 : Fin 32) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = sq := by rw [P13.regs (20 : Fin 32) (by decide), g12_20]
  have g13_26 : reg n13 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P13.regs (26 : Fin 32) (by decide), g12_26]
  have keep_kk13 : P2vKeepL B n0.mem n13.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_98 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := (K13.w32 (by decide) (by decide)).trans w12_98
  have w13_c80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := (K13.w32 (by decide) (by decide)).trans w12_c80
  have b13_dc : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := (K13.b8 (by decide) (by decide)).trans b12_dc
  have a13_58 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K13.acc (by decide) (by decide)).trans a12_58
  have a13_78 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K13.acc (by decide) (by decide)).trans a12_78
  have a13_9c : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K13.acc (by decide) (by decide)).trans a12_9c
  have a13_bc : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K13.acc (by decide) (by decide)).trans a12_bc
  have a13_c84 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 rp 32) := (K13.acc (by decide) (by decide)).trans a12_c84
  have a13_200 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (accV_S 8 fun q hq => by
    rw [show 0x200 + q = 0x200 + (0x0 + q) by omega, X13 (0x0 + q) (by omega),
      show 0xC84 + (0x0 + q) = 0xC84 + q by omega]).trans a12_c84
  clear a12_c84 a12_bc a12_9c a12_78 a12_58 b12_dc w12_c80 w12_98 g12_12 g12_11 g12_10 g12_26 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0xE8
  obtain ⟨n14, c14, u14⟩ := s13.block p2vA2e8 E13.self p2vA2e8_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem P2V n14 0xF2 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock p2vA2e8 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
  have fr14 : ∀ x, P2vR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans c14
  have fR14 : ∀ x, P2vR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : P2vCode n14.mem := E13.fr F fr14
  have V14 : P2vSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by
    rw [rb14, runBlock_reg _ _ _ sp s13.zero (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb14, runBlock_reg _ _ _ (3 : Fin 32) s13.zero (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb14, runBlock_reg _ _ _ (4 : Fin 32) s13.zero (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = rp := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = pk := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = dg := by
    rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = sq := by
    rw [rb14, runBlock_reg _ _ _ (20 : Fin 32) s13.zero (by decide), g13_20]
  have g14_26 : reg n14 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vA2e8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_26, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_11 : reg n14 a1 = sq := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vA2e8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_26, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk14 : P2vKeepL B n0.mem n14.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m14]; exact w13_98
  have w14_c80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m14]; exact w13_c80
  have b14_dc : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m14]; exact b13_dc
  have a14_58 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m14]; exact a13_58
  have a14_78 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m14]; exact a13_78
  have a14_9c : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m14]; exact a13_9c
  have a14_bc : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m14]; exact a13_bc
  have a14_200 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m14]; exact a13_200
  have a14_c84 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 rp 32) := by rw [m14]; exact a13_c84
  clear a13_200 a13_c84 a13_bc a13_9c a13_78 a13_58 b13_dc w13_c80 w13_98 g13_26 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 s13 X13 K13 P13
  -- 0xF2: p2v_sf2P
  obtain ⟨n15, c15, s15, sp15, rk15, L15, G15, K15, fr15⟩ := p2v_sf2P (co := 0xC80)
    F E14 (BG0.p2v F fR14) s14 p2v_at_f2 p2v_at_f6 (by decide) (by decide) g14_2
    g14_10 g14_11 (by decide) (by decide) s_in
  rw [p2v_mb fR14 s_in] at L15 G15
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, P2vR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : P2vCode n15.mem := E14.fr F fr15
  have V15 : P2vSaves B n15.mem v := V14.keepL K15 (by decide)
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk15 (3 : Fin 32) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk15 (4 : Fin 32) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = rp := by rw [rk15 (8 : Fin 32) (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = pk := by rw [rk15 (9 : Fin 32) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk15 (18 : Fin 32) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = dg := by rw [rk15 (19 : Fin 32) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = sq := by rw [rk15 (20 : Fin 32) (by decide), g14_20]
  have g15_26 : reg n15 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk15 (26 : Fin 32) (by decide), g14_26]
  have g15_2 : reg n15 sp = B + 0x21A0 := sp15
  by_cases hls : beNat (memBytes M0 sq 32) < C3.p256.n
  rotate_left
  · have z15 := G15 (Nat.le_of_not_lt hls)
    have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24)] := keep_kk14.trans K15
    clear keep_kk14
    have w15_98 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := (K15.w32 (by decide) (by decide)).trans w14_98
    have b15_dc : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := (K15.b8 (by decide) (by decide)).trans b14_dc
    have a15_58 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K15.acc (by decide) (by decide)).trans a14_58
    have a15_78 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K15.acc (by decide) (by decide)).trans a14_78
    have a15_9c : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K15.acc (by decide) (by decide)).trans a14_9c
    have a15_bc : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K15.acc (by decide) (by decide)).trans a14_bc
    have a15_200 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K15.acc (by decide) (by decide)).trans a14_200
    have w15_c80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 1 := z15
    clear a14_c84 a14_200 a14_bc a14_9c a14_78 a14_58 b14_dc w14_c80 w14_98 g14_11 g14_10 g14_26 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
    -- 0xFA: lw
    obtain ⟨n16, d16, u16⟩ := s15.lw E15.self p2v_at_fa (off' := 0xFE) (by decide)
      (by rw [g15_26, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x360 = B + 0x21A0 + BitVec.ofNat 32 0xC80 by p2v_addr]; exact p2v_al F (by decide) (by decide))
    have s16 : St n16.mem P2V n16 0xFE (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, P2vR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, P2vR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : P2vCode n16.mem := E15.fr F fr16
    have V16 : P2vSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
    have g16_8 : reg n16 (8 : Fin 32) = rp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_8]
    have g16_9 : reg n16 (9 : Fin 32) = pk := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
    have g16_18 : reg n16 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = dg := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = sq := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
    have g16_26 : reg n16 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
    have g16_10 : reg n16 a0 = 1 := by
      rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g15_26, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x360 = B + 0x21A0 + BitVec.ofNat 32 0xC80 by p2v_addr, w15_c80]
    have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m16]; exact w15_98
    have w16_c80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 1 := by rw [m16]; exact w15_c80
    have b16_dc : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m16]; exact b15_dc
    have a16_58 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m16]; exact a15_58
    have a16_78 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m16]; exact a15_78
    have a16_9c : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m16]; exact a15_9c
    have a16_bc : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m16]; exact a15_bc
    have a16_200 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m16]; exact a15_200
    clear w15_c80 a15_200 a15_bc a15_9c a15_78 a15_58 b15_dc w15_98 z15
    -- 0xFE: branch, taken
    obtain ⟨n17, d17, u17⟩ := s16.taken E16.self 0x142 p2v_at_fe
      (by decide) (by rw [g16_10, s16.zero]; decide)
    have s17 : St n17.mem P2V n17 0x142 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, P2vR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, P2vR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : P2vCode n17.mem := E16.fr F fr17
    have V17 : P2vSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = rp := by rw [u17.regs, g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = pk := by rw [u17.regs, g16_9]
    have g17_10 : reg n17 a0 = 1 := by rw [u17.regs, g16_10]
    have g17_18 : reg n17 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = dg := by rw [u17.regs, g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = sq := by rw [u17.regs, g16_20]
    have g17_26 : reg n17 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u17.regs, g16_26]
    have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m17]; exact w16_98
    have w17_c80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 1 := by rw [m17]; exact w16_c80
    have b17_dc : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m17]; exact b16_dc
    have a17_58 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m17]; exact a16_58
    have a17_78 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m17]; exact a16_78
    have a17_9c : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m17]; exact a16_9c
    have a17_bc : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m17]; exact a16_bc
    have a17_200 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m17]; exact a16_200
    clear a16_200 a16_bc a16_9c a16_78 a16_58 b16_dc w16_c80 w16_98 g16_10 g16_26 g16_20 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    exact .inl ⟨(fun ⟨h0', h1', h2', _⟩ => by exact hls h2'), p2v_fail F E17 s17 t17 (fun x hx => (fR17 x hx).trans (fM x hx).symm) V17 hret g17_2 g17_3 g17_4⟩
  obtain ⟨z15, y15⟩ := L15 hls
  have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24)] := keep_kk14.trans K15
  clear keep_kk14
  have w15_98 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := (K15.w32 (by decide) (by decide)).trans w14_98
  have b15_dc : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := (K15.b8 (by decide) (by decide)).trans b14_dc
  have a15_58 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K15.acc (by decide) (by decide)).trans a14_58
  have a15_78 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K15.acc (by decide) (by decide)).trans a14_78
  have a15_9c : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K15.acc (by decide) (by decide)).trans a14_9c
  have a15_bc : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K15.acc (by decide) (by decide)).trans a14_bc
  have a15_200 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K15.acc (by decide) (by decide)).trans a14_200
  have a15_c84 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [show B + 0x21A0 + BitVec.ofNat 32 0xC84 = B + 0x21A0 + BitVec.ofNat 32 0xC80 + 4 by p2v_addr]; exact y15
  have w15_c80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := z15
  clear a14_c84 a14_200 a14_bc a14_9c a14_78 a14_58 b14_dc w14_c80 w14_98 g14_11 g14_10 g14_26 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0xFA: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self p2v_at_fa (off' := 0xFE) (by decide)
    (by rw [g15_26, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x360 = B + 0x21A0 + BitVec.ofNat 32 0xC80 by p2v_addr]; exact p2v_al F (by decide) (by decide))
  have s16 : St n16.mem P2V n16 0xFE (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, P2vR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, P2vR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : P2vCode n16.mem := E15.fr F fr16
  have V16 : P2vSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = rp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = pk := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = dg := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = sq := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
  have g16_26 : reg n16 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
  have g16_10 : reg n16 a0 = 0 := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_26, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x360 = B + 0x21A0 + BitVec.ofNat 32 0xC80 by p2v_addr, w15_c80]
  have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m16]; exact w15_98
  have w16_c80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m16]; exact w15_c80
  have b16_dc : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m16]; exact b15_dc
  have a16_58 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m16]; exact a15_58
  have a16_78 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m16]; exact a15_78
  have a16_9c : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m16]; exact a15_9c
  have a16_bc : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m16]; exact a15_bc
  have a16_200 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m16]; exact a15_200
  have a16_c84 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m16]; exact a15_c84
  clear w15_c80 a15_c84 a15_200 a15_bc a15_9c a15_78 a15_58 b15_dc w15_98 y15 z15 g15_2 g15_26 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 V15 E15 fR15 t15 fr15 K15 G15 L15 rk15 sp15 s15 c15
  -- 0xFE: branch, not taken
  obtain ⟨n17, d17, u17⟩ := s16.notTaken E16.self 0x100 p2v_at_fe
    (by decide) (by rw [g16_10, s16.zero]; decide)
  have s17 : St n17.mem P2V n17 0x100 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, P2vR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, P2vR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : P2vCode n17.mem := E16.fr F fr17
  have V17 : P2vSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = rp := by rw [u17.regs, g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = pk := by rw [u17.regs, g16_9]
  have g17_10 : reg n17 a0 = 0 := by rw [u17.regs, g16_10]
  have g17_18 : reg n17 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u17.regs, g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = dg := by rw [u17.regs, g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = sq := by rw [u17.regs, g16_20]
  have g17_26 : reg n17 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u17.regs, g16_26]
  have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m17]; exact w16_98
  have w17_c80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m17]; exact w16_c80
  have b17_dc : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m17]; exact b16_dc
  have a17_58 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m17]; exact a16_58
  have a17_78 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m17]; exact a16_78
  have a17_9c : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m17]; exact a16_9c
  have a17_bc : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m17]; exact a16_bc
  have a17_200 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m17]; exact a16_200
  have a17_c84 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m17]; exact a16_c84
  clear a16_c84 a16_200 a16_bc a16_9c a16_78 a16_58 b16_dc w16_c80 w16_98 g16_10 g16_26 g16_20 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0x100
  obtain ⟨n18, c18, u18⟩ := s17.block p2vA2100 E17.self p2vA2100_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem P2V n18 0x114 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock p2vA2100 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
  have fr18 : ∀ x, P2vR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans c18
  have fR18 : ∀ x, P2vR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : P2vCode n18.mem := E17.fr F fr18
  have V18 : P2vSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by
    rw [rb18, runBlock_reg _ _ _ sp s17.zero (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (3 : Fin 32) s17.zero (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (4 : Fin 32) s17.zero (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = rp := by
    rw [rb18, runBlock_reg _ _ _ (8 : Fin 32) s17.zero (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = pk := by
    rw [rb18, runBlock_reg _ _ _ (9 : Fin 32) s17.zero (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb18, runBlock_reg _ _ _ (18 : Fin 32) s17.zero (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = dg := by
    rw [rb18, runBlock_reg _ _ _ (19 : Fin 32) s17.zero (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = sq := by
    rw [rb18, runBlock_reg _ _ _ (20 : Fin 32) s17.zero (by decide), g17_20]
  have g18_26 : reg n18 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
  have g18_10 : reg n18 a0 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, p2vA2100, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_10, g17_18, g17_19, g17_20, g17_26, s17.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g18_11 : reg n18 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, p2vA2100, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_10, g17_18, g17_19, g17_20, g17_26, s17.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g18_12 : reg n18 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, p2vA2100, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_10, g17_18, g17_19, g17_20, g17_26, s17.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk18 : P2vKeepL B n0.mem n18.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_98 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m18]; exact w17_98
  have w18_c80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m18]; exact w17_c80
  have b18_dc : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m18]; exact b17_dc
  have a18_58 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m18]; exact a17_58
  have a18_78 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m18]; exact a17_78
  have a18_9c : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m18]; exact a17_9c
  have a18_bc : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m18]; exact a17_bc
  have a18_200 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m18]; exact a17_200
  have a18_c84 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m18]; exact a17_c84
  clear a17_c84 a17_200 a17_bc a17_9c a17_78 a17_58 b17_dc w17_c80 w17_98 g17_26 g17_20 g17_19 g17_18 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0x114: memcpy
  obtain ⟨n19, P19, K19, X19⟩ := p2v_mc (c := 0xFE4) (d := 0xC84) (N := 0x20) F E18 s18 p2v_at_114 p2v_at_118
    (by decide) (by decide) g18_2 g18_10 g18_11 g18_12
    (by decide) (by decide) (by decide)
  have s19 := P19.st
  have fr19 := P19.fr
  have t19 : Steps n0 n19 := t18.trans P19.steps
  have fR19 : ∀ x, P2vR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : P2vCode n19.mem := E18.fr F fr19
  have V19 : P2vSaves B n19.mem v := V18.keep K19 (by decide)
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [P19.regs sp (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P19.regs (3 : Fin 32) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P19.regs (4 : Fin 32) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = rp := by rw [P19.regs (8 : Fin 32) (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = pk := by rw [P19.regs (9 : Fin 32) (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P19.regs (18 : Fin 32) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = dg := by rw [P19.regs (19 : Fin 32) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = sq := by rw [P19.regs (20 : Fin 32) (by decide), g18_20]
  have g19_26 : reg n19 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P19.regs (26 : Fin 32) (by decide), g18_26]
  have keep_kk19 : P2vKeepL B n0.mem n19.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := keep_kk18.trans K19.toL
  clear keep_kk18
  have w19_98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := (K19.w32 (by decide) (by decide)).trans w18_98
  have w19_c80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := (K19.w32 (by decide) (by decide)).trans w18_c80
  have b19_dc : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := (K19.b8 (by decide) (by decide)).trans b18_dc
  have a19_58 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K19.acc (by decide) (by decide)).trans a18_58
  have a19_78 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K19.acc (by decide) (by decide)).trans a18_78
  have a19_9c : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K19.acc (by decide) (by decide)).trans a18_9c
  have a19_bc : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K19.acc (by decide) (by decide)).trans a18_bc
  have a19_200 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K19.acc (by decide) (by decide)).trans a18_200
  have a19_c84 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := (K19.acc (by decide) (by decide)).trans a18_c84
  have a19_fe4 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (accV_S 8 fun q hq => by
    rw [show 0xFE4 + q = 0xFE4 + (0x0 + q) by omega, X19 (0x0 + q) (by omega),
      show 0xC84 + (0x0 + q) = 0xC84 + q by omega]).trans a18_c84
  clear a18_c84 a18_200 a18_bc a18_9c a18_78 a18_58 b18_dc w18_c80 w18_98 g18_12 g18_11 g18_10 g18_26 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  -- 0x11C
  obtain ⟨n20, c20, u20⟩ := s19.block p2vA211c E19.self p2vA211c_end
    ⟨trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem P2V n20 0x11E (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock p2vA211c (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
  have fr20 : ∀ x, P2vR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, P2vR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : P2vCode n20.mem := E19.fr F fr20
  have V20 : P2vSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by
    rw [rb20, runBlock_reg _ _ _ sp s19.zero (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb20, runBlock_reg _ _ _ (3 : Fin 32) s19.zero (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb20, runBlock_reg _ _ _ (4 : Fin 32) s19.zero (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = rp := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = pk := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = dg := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = sq := by
    rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
  have g20_26 : reg n20 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, p2vA211c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_18, g19_19, g19_20, g19_26, s19.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk20 : P2vKeepL B n0.mem n20.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m20]; exact w19_98
  have w20_c80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m20]; exact w19_c80
  have b20_dc : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m20]; exact b19_dc
  have a20_58 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m20]; exact a19_58
  have a20_78 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m20]; exact a19_78
  have a20_9c : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m20]; exact a19_9c
  have a20_bc : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m20]; exact a19_bc
  have a20_200 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m20]; exact a19_200
  have a20_c84 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m20]; exact a19_c84
  have a20_fe4 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m20]; exact a19_fe4
  clear a19_fe4 a19_c84 a19_200 a19_bc a19_9c a19_78 a19_58 b19_dc w19_c80 w19_98 g19_26 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 s19 X19 K19 P19
  -- 0x11E: p2v_szF
  obtain ⟨n21, c21, s21, sp21, rk21, a0_21, K21, fr21⟩ := p2v_szF (oc := 0x200)
    F E20 (EC0.p2v F fR20) s20 p2v_at_11e p2v_at_122 (by decide) (by decide) g20_2
    g20_10 (by decide) (by decide)
  simp only [limbs0_iff a20_200] at a0_21
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, P2vR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : P2vCode n21.mem := E20.fr F fr21
  have V21 : P2vSaves B n21.mem v := V20.keepL K21 (by decide)
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk21 (3 : Fin 32) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk21 (4 : Fin 32) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = rp := by rw [rk21 (8 : Fin 32) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = pk := by rw [rk21 (9 : Fin 32) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk21 (18 : Fin 32) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = dg := by rw [rk21 (19 : Fin 32) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = sq := by rw [rk21 (20 : Fin 32) (by decide), g20_20]
  have g21_26 : reg n21 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk21 (26 : Fin 32) (by decide), g20_26]
  have g21_2 : reg n21 sp = B + 0x21A0 := sp21
  have keep_kk21 : P2vKeepL B n0.mem n21.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := keep_kk20.trans K21
  clear keep_kk20
  have w21_98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := (K21.w32 (by decide) (by decide)).trans w20_98
  have w21_c80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := (K21.w32 (by decide) (by decide)).trans w20_c80
  have b21_dc : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := (K21.b8 (by decide) (by decide)).trans b20_dc
  have a21_58 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K21.acc (by decide) (by decide)).trans a20_58
  have a21_78 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K21.acc (by decide) (by decide)).trans a20_78
  have a21_9c : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K21.acc (by decide) (by decide)).trans a20_9c
  have a21_bc : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K21.acc (by decide) (by decide)).trans a20_bc
  have a21_200 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K21.acc (by decide) (by decide)).trans a20_200
  have a21_c84 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := (K21.acc (by decide) (by decide)).trans a20_c84
  have a21_fe4 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K21.acc (by decide) (by decide)).trans a20_fe4
  clear a20_fe4 a20_c84 a20_200 a20_bc a20_9c a20_78 a20_58 b20_dc w20_c80 w20_98 g20_10 g20_26 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  by_cases hzr : beNat (memBytes M0 rp 32) ≠ 0
  rotate_left
  · have g21_10 : reg n21 a0 = BitVec.ofNat 32 1 := by rw [a0_21, ite_eq_left (Decidable.of_not_not hzr)]; rfl
    -- 0x126
    obtain ⟨n22, c22, u22⟩ := s21.block p2vA2126 E21.self p2vA2126_end
      ⟨trivial, trivial⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have s22 : St n22.mem P2V n22 0x12A (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have rb22 : ∀ q, reg n22 q = (runBlock p2vA2126 (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
    have fr22 : ∀ x, P2vR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans c22
    have fR22 : ∀ x, P2vR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : P2vCode n22.mem := E21.fr F fr22
    have V22 : P2vSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by
      rw [rb22, runBlock_reg _ _ _ sp s21.zero (by decide), g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb22, runBlock_reg _ _ _ (3 : Fin 32) s21.zero (by decide), g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb22, runBlock_reg _ _ _ (4 : Fin 32) s21.zero (by decide), g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = rp := by
      rw [rb22, runBlock_reg _ _ _ (8 : Fin 32) s21.zero (by decide), g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = pk := by
      rw [rb22, runBlock_reg _ _ _ (9 : Fin 32) s21.zero (by decide), g21_9]
    have g22_18 : reg n22 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
      rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = dg := by
      rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = sq := by
      rw [rb22, runBlock_reg _ _ _ (20 : Fin 32) s21.zero (by decide), g21_20]
    have g22_26 : reg n22 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
      rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
    have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb22]; simp +decide only [runBlock, BInstr.run, p2vA2126, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_10, g21_18, g21_19, g21_20, g21_26, s21.zero])
      all_goals first | with_reducible rfl | p2v_addr | decide
    have keep_kk22 : P2vKeepL B n0.mem n22.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_98 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m22]; exact w21_98
    have w22_c80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m22]; exact w21_c80
    have b22_dc : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m22]; exact b21_dc
    have a22_58 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m22]; exact a21_58
    have a22_78 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m22]; exact a21_78
    have a22_9c : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m22]; exact a21_9c
    have a22_bc : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m22]; exact a21_bc
    have a22_200 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m22]; exact a21_200
    have a22_c84 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m22]; exact a21_c84
    have a22_fe4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m22]; exact a21_fe4
    clear a21_fe4 a21_c84 a21_200 a21_bc a21_9c a21_78 a21_58 b21_dc w21_c80 w21_98 g21_2 g21_26 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 V21 E21 fR21 t21 fr21 K21 a0_21 rk21 sp21 s21 c21
    -- 0x12A: branch, taken
    obtain ⟨n23, d23, u23⟩ := s22.taken E22.self 0x142 p2v_at_12a
      (by decide) (by rw [g22_10, s22.zero]; decide)
    have s23 : St n23.mem P2V n23 0x142 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have fr23 : ∀ x, P2vR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
    have t23 : Steps n0 n23 := t22.trans (.single d23)
    have fR23 : ∀ x, P2vR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : P2vCode n23.mem := E22.fr F fr23
    have V23 : P2vSaves B n23.mem v := V22.same m23
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, g22_4]
    have g23_8 : reg n23 (8 : Fin 32) = rp := by rw [u23.regs, g22_8]
    have g23_9 : reg n23 (9 : Fin 32) = pk := by rw [u23.regs, g22_9]
    have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x1 := by rw [u23.regs, g22_10]
    have g23_18 : reg n23 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u23.regs, g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = dg := by rw [u23.regs, g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = sq := by rw [u23.regs, g22_20]
    have g23_26 : reg n23 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u23.regs, g22_26]
    have keep_kk23 : P2vKeepL B n0.mem n23.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_98 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m23]; exact w22_98
    have w23_c80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m23]; exact w22_c80
    have b23_dc : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m23]; exact b22_dc
    have a23_58 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m23]; exact a22_58
    have a23_78 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m23]; exact a22_78
    have a23_9c : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m23]; exact a22_9c
    have a23_bc : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m23]; exact a22_bc
    have a23_200 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m23]; exact a22_200
    have a23_c84 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m23]; exact a22_c84
    have a23_fe4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m23]; exact a22_fe4
    clear a22_fe4 a22_c84 a22_200 a22_bc a22_9c a22_78 a22_58 b22_dc w22_c80 w22_98 g22_10 g22_26 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22 g21_10
    exact .inl ⟨(fun ⟨h0', h1', h2', h3', _⟩ => by exact hzr h3'), p2v_fail F E23 s23 t23 (fun x hx => (fR23 x hx).trans (fM x hx).symm) V23 hret g23_2 g23_3 g23_4⟩
  have g21_10 : reg n21 a0 = BitVec.ofNat 32 0 := by rw [a0_21, ite_eq_right hzr]; rfl
  -- 0x126
  obtain ⟨n22, c22, u22⟩ := s21.block p2vA2126 E21.self p2vA2126_end
    ⟨trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem P2V n22 0x12A (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock p2vA2126 (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
  have fr22 : ∀ x, P2vR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans c22
  have fR22 : ∀ x, P2vR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : P2vCode n22.mem := E21.fr F fr22
  have V22 : P2vSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by
    rw [rb22, runBlock_reg _ _ _ sp s21.zero (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb22, runBlock_reg _ _ _ (3 : Fin 32) s21.zero (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb22, runBlock_reg _ _ _ (4 : Fin 32) s21.zero (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = rp := by
    rw [rb22, runBlock_reg _ _ _ (8 : Fin 32) s21.zero (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = pk := by
    rw [rb22, runBlock_reg _ _ _ (9 : Fin 32) s21.zero (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = dg := by
    rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = sq := by
    rw [rb22, runBlock_reg _ _ _ (20 : Fin 32) s21.zero (by decide), g21_20]
  have g22_26 : reg n22 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, p2vA2126, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_10, g21_18, g21_19, g21_20, g21_26, s21.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk22 : P2vKeepL B n0.mem n22.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_98 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m22]; exact w21_98
  have w22_c80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m22]; exact w21_c80
  have b22_dc : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m22]; exact b21_dc
  have a22_58 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m22]; exact a21_58
  have a22_78 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m22]; exact a21_78
  have a22_9c : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m22]; exact a21_9c
  have a22_bc : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m22]; exact a21_bc
  have a22_200 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m22]; exact a21_200
  have a22_c84 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m22]; exact a21_c84
  have a22_fe4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m22]; exact a21_fe4
  clear a21_fe4 a21_c84 a21_200 a21_bc a21_9c a21_78 a21_58 b21_dc w21_c80 w21_98 g21_2 g21_26 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 V21 E21 fR21 t21 fr21 K21 a0_21 rk21 sp21 s21 c21
  -- 0x12A: branch, not taken
  obtain ⟨n23, d23, u23⟩ := s22.notTaken E22.self 0x12C p2v_at_12a
    (by decide) (by rw [g22_10, s22.zero]; decide)
  have s23 : St n23.mem P2V n23 0x12C (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, P2vR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, P2vR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : P2vCode n23.mem := E22.fr F fr23
  have V23 : P2vSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = rp := by rw [u23.regs, g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = pk := by rw [u23.regs, g22_9]
  have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x0 := by rw [u23.regs, g22_10]
  have g23_18 : reg n23 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u23.regs, g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = dg := by rw [u23.regs, g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = sq := by rw [u23.regs, g22_20]
  have g23_26 : reg n23 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u23.regs, g22_26]
  have keep_kk23 : P2vKeepL B n0.mem n23.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_98 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m23]; exact w22_98
  have w23_c80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m23]; exact w22_c80
  have b23_dc : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m23]; exact b22_dc
  have a23_58 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m23]; exact a22_58
  have a23_78 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m23]; exact a22_78
  have a23_9c : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m23]; exact a22_9c
  have a23_bc : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m23]; exact a22_bc
  have a23_200 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m23]; exact a22_200
  have a23_c84 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m23]; exact a22_c84
  have a23_fe4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m23]; exact a22_fe4
  clear a22_fe4 a22_c84 a22_200 a22_bc a22_9c a22_78 a22_58 b22_dc w22_c80 w22_98 g22_10 g22_26 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22 g21_10
  -- 0x12C
  obtain ⟨n24, c24, u24⟩ := s23.block p2vA212c E23.self p2vA212c_end
    ⟨trivial, trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem P2V n24 0x134 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock p2vA212c (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
  have fr24 : ∀ x, P2vR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans c24
  have fR24 : ∀ x, P2vR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : P2vCode n24.mem := E23.fr F fr24
  have V24 : P2vSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by
    rw [rb24, runBlock_reg _ _ _ sp s23.zero (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (3 : Fin 32) s23.zero (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (4 : Fin 32) s23.zero (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = rp := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = pk := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = dg := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = sq := by
    rw [rb24, runBlock_reg _ _ _ (20 : Fin 32) s23.zero (by decide), g23_20]
  have g24_26 : reg n24 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_10 : reg n24 a0 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, p2vA212c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_18, g23_19, g23_20, g23_26, s23.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk24 : P2vKeepL B n0.mem n24.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_98 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m24]; exact w23_98
  have w24_c80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m24]; exact w23_c80
  have b24_dc : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m24]; exact b23_dc
  have a24_58 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m24]; exact a23_58
  have a24_78 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m24]; exact a23_78
  have a24_9c : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m24]; exact a23_9c
  have a24_bc : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m24]; exact a23_bc
  have a24_200 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m24]; exact a23_200
  have a24_c84 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m24]; exact a23_c84
  have a24_fe4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m24]; exact a23_fe4
  clear a23_fe4 a23_c84 a23_200 a23_bc a23_9c a23_78 a23_58 b23_dc w23_c80 w23_98 g23_26 g23_20 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0x134: p2v_szF
  obtain ⟨n25, c25, s25, sp25, rk25, a0_25, K25, fr25⟩ := p2v_szF (oc := 0xFE4)
    F E24 (EC0.p2v F fR24) s24 p2v_at_134 p2v_at_138 (by decide) (by decide) g24_2
    g24_10 (by decide) (by decide)
  simp only [limbs0_iff a24_fe4] at a0_25
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, P2vR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : P2vCode n25.mem := E24.fr F fr25
  have V25 : P2vSaves B n25.mem v := V24.keepL K25 (by decide)
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk25 (3 : Fin 32) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk25 (4 : Fin 32) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = rp := by rw [rk25 (8 : Fin 32) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = pk := by rw [rk25 (9 : Fin 32) (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk25 (18 : Fin 32) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = dg := by rw [rk25 (19 : Fin 32) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = sq := by rw [rk25 (20 : Fin 32) (by decide), g24_20]
  have g25_26 : reg n25 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk25 (26 : Fin 32) (by decide), g24_26]
  have g25_2 : reg n25 sp = B + 0x21A0 := sp25
  have keep_kk25 : P2vKeepL B n0.mem n25.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := keep_kk24.trans K25
  clear keep_kk24
  have w25_98 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := (K25.w32 (by decide) (by decide)).trans w24_98
  have w25_c80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := (K25.w32 (by decide) (by decide)).trans w24_c80
  have b25_dc : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := (K25.b8 (by decide) (by decide)).trans b24_dc
  have a25_58 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K25.acc (by decide) (by decide)).trans a24_58
  have a25_78 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K25.acc (by decide) (by decide)).trans a24_78
  have a25_9c : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K25.acc (by decide) (by decide)).trans a24_9c
  have a25_bc : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K25.acc (by decide) (by decide)).trans a24_bc
  have a25_200 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K25.acc (by decide) (by decide)).trans a24_200
  have a25_c84 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := (K25.acc (by decide) (by decide)).trans a24_c84
  have a25_fe4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K25.acc (by decide) (by decide)).trans a24_fe4
  clear a24_fe4 a24_c84 a24_200 a24_bc a24_9c a24_78 a24_58 b24_dc w24_c80 w24_98 g24_10 g24_26 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  by_cases hzs : beNat (memBytes M0 sq 32) ≠ 0
  rotate_left
  · have g25_10 : reg n25 a0 = BitVec.ofNat 32 1 := by rw [a0_25, ite_eq_left (Decidable.of_not_not hzs)]; rfl
    -- 0x13C
    obtain ⟨n26, c26, u26⟩ := s25.block p2vA213c E25.self p2vA213c_end
      ⟨trivial, trivial⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have s26 : St n26.mem P2V n26 0x140 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have rb26 : ∀ q, reg n26 q = (runBlock p2vA213c (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
    have fr26 : ∀ x, P2vR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans c26
    have fR26 : ∀ x, P2vR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : P2vCode n26.mem := E25.fr F fr26
    have V26 : P2vSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by
      rw [rb26, runBlock_reg _ _ _ sp s25.zero (by decide), g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb26, runBlock_reg _ _ _ (3 : Fin 32) s25.zero (by decide), g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb26, runBlock_reg _ _ _ (4 : Fin 32) s25.zero (by decide), g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = rp := by
      rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = pk := by
      rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
    have g26_18 : reg n26 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
      rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = dg := by
      rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
    have g26_20 : reg n26 (20 : Fin 32) = sq := by
      rw [rb26, runBlock_reg _ _ _ (20 : Fin 32) s25.zero (by decide), g25_20]
    have g26_26 : reg n26 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
      rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
    have g26_10 : reg n26 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb26]; simp +decide only [runBlock, BInstr.run, p2vA213c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_18, g25_19, g25_20, g25_26, s25.zero])
      all_goals first | with_reducible rfl | p2v_addr | decide
    have keep_kk26 : P2vKeepL B n0.mem n26.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := by rw [m26]; exact keep_kk25
    clear keep_kk25
    have w26_98 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m26]; exact w25_98
    have w26_c80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m26]; exact w25_c80
    have b26_dc : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m26]; exact b25_dc
    have a26_58 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m26]; exact a25_58
    have a26_78 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m26]; exact a25_78
    have a26_9c : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m26]; exact a25_9c
    have a26_bc : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m26]; exact a25_bc
    have a26_200 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m26]; exact a25_200
    have a26_c84 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m26]; exact a25_c84
    have a26_fe4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m26]; exact a25_fe4
    clear a25_fe4 a25_c84 a25_200 a25_bc a25_9c a25_78 a25_58 b25_dc w25_c80 w25_98 g25_2 g25_26 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 V25 E25 fR25 t25 fr25 K25 a0_25 rk25 sp25 s25 c25
    -- 0x140: branch, not taken
    obtain ⟨n27, d27, u27⟩ := s26.notTaken E26.self 0x142 p2v_at_140
      (by decide) (by rw [g26_10, s26.zero]; decide)
    have s27 : St n27.mem P2V n27 0x142 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, P2vR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, P2vR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : P2vCode n27.mem := E26.fr F fr27
    have V27 : P2vSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = rp := by rw [u27.regs, g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = pk := by rw [u27.regs, g26_9]
    have g27_10 : reg n27 a0 = BitVec.ofNat 32 0x1 := by rw [u27.regs, g26_10]
    have g27_18 : reg n27 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u27.regs, g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = dg := by rw [u27.regs, g26_19]
    have g27_20 : reg n27 (20 : Fin 32) = sq := by rw [u27.regs, g26_20]
    have g27_26 : reg n27 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u27.regs, g26_26]
    have keep_kk27 : P2vKeepL B n0.mem n27.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := by rw [m27]; exact keep_kk26
    clear keep_kk26
    have w27_98 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m27]; exact w26_98
    have w27_c80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m27]; exact w26_c80
    have b27_dc : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m27]; exact b26_dc
    have a27_58 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m27]; exact a26_58
    have a27_78 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m27]; exact a26_78
    have a27_9c : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m27]; exact a26_9c
    have a27_bc : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m27]; exact a26_bc
    have a27_200 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m27]; exact a26_200
    have a27_c84 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m27]; exact a26_c84
    have a27_fe4 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m27]; exact a26_fe4
    clear a26_fe4 a26_c84 a26_200 a26_bc a26_9c a26_78 a26_58 b26_dc w26_c80 w26_98 g26_10 g26_26 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26 g25_10
    exact .inl ⟨(fun ⟨h0', h1', h2', h3', h4', _⟩ => by exact hzs h4'), p2v_fail F E27 s27 t27 (fun x hx => (fR27 x hx).trans (fM x hx).symm) V27 hret g27_2 g27_3 g27_4⟩
  have g25_10 : reg n25 a0 = BitVec.ofNat 32 0 := by rw [a0_25, ite_eq_right hzs]; rfl
  -- 0x13C
  obtain ⟨n26, c26, u26⟩ := s25.block p2vA213c E25.self p2vA213c_end
    ⟨trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem P2V n26 0x140 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock p2vA213c (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
  have fr26 : ∀ x, P2vR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans c26
  have fR26 : ∀ x, P2vR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : P2vCode n26.mem := E25.fr F fr26
  have V26 : P2vSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by
    rw [rb26, runBlock_reg _ _ _ sp s25.zero (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb26, runBlock_reg _ _ _ (3 : Fin 32) s25.zero (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb26, runBlock_reg _ _ _ (4 : Fin 32) s25.zero (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = rp := by
    rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = pk := by
    rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = dg := by
    rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = sq := by
    rw [rb26, runBlock_reg _ _ _ (20 : Fin 32) s25.zero (by decide), g25_20]
  have g26_26 : reg n26 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
  have g26_10 : reg n26 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, p2vA213c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_18, g25_19, g25_20, g25_26, s25.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk26 : P2vKeepL B n0.mem n26.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_98 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m26]; exact w25_98
  have w26_c80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m26]; exact w25_c80
  have b26_dc : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m26]; exact b25_dc
  have a26_58 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m26]; exact a25_58
  have a26_78 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m26]; exact a25_78
  have a26_9c : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m26]; exact a25_9c
  have a26_bc : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m26]; exact a25_bc
  have a26_200 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m26]; exact a25_200
  have a26_c84 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m26]; exact a25_c84
  have a26_fe4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m26]; exact a25_fe4
  clear a25_fe4 a25_c84 a25_200 a25_bc a25_9c a25_78 a25_58 b25_dc w25_c80 w25_98 g25_2 g25_26 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 V25 E25 fR25 t25 fr25 K25 a0_25 rk25 sp25 s25 c25
  -- 0x140: branch, taken
  obtain ⟨n27, d27, u27⟩ := s26.taken E26.self 0x186 p2v_at_140
    (by decide) (by rw [g26_10, s26.zero]; decide)
  have s27 : St n27.mem P2V n27 0x186 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, P2vR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, P2vR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : P2vCode n27.mem := E26.fr F fr27
  have V27 : P2vSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = rp := by rw [u27.regs, g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = pk := by rw [u27.regs, g26_9]
  have g27_10 : reg n27 a0 = BitVec.ofNat 32 0x0 := by rw [u27.regs, g26_10]
  have g27_18 : reg n27 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [u27.regs, g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = dg := by rw [u27.regs, g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = sq := by rw [u27.regs, g26_20]
  have g27_26 : reg n27 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u27.regs, g26_26]
  have keep_kk27 : P2vKeepL B n0.mem n27.mem [(0x98, 0x48), (0x58, 0x40), (0xC80, 0x24), (0x200, 0x20), (0xC80, 0x24), (0xFE4, 0x20)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_98 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = 0 := by rw [m27]; exact w26_98
  have w27_c80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = 0 := by rw [m27]; exact w26_c80
  have b27_dc : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (0 : BitVec 8) := by rw [m27]; exact b26_dc
  have a27_58 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m27]; exact a26_58
  have a27_78 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m27]; exact a26_78
  have a27_9c : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m27]; exact a26_9c
  have a27_bc : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m27]; exact a26_bc
  have a27_200 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m27]; exact a26_200
  have a27_c84 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 8 = beNat (memBytes M0 sq 32) := by rw [m27]; exact a26_c84
  have a27_fe4 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m27]; exact a26_fe4
  clear a26_fe4 a26_c84 a26_200 a26_bc a26_9c a26_78 a26_58 b26_dc w26_c80 w26_98 g26_10 g26_26 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26 g25_10
  exact .inr ⟨hgs, hlr, hls, hzr, hzs, n27, t27, s27, E27, V27, fR27, g27_2, g27_3, g27_4, g27_18, g27_19, g27_26, a27_58, a27_78, a27_9c, a27_bc, a27_200, a27_c84, a27_fe4, keep_kk27.mono (by decide)⟩

end C3.RV32.P2v
