import C3BootProofs.Proofs.P2vIvLib

/-!
# `p256VerifyPrehash`: the start of a batch of the inversion of `s`

From the scan's end at 0x3F8 to the divstep loop at 0x43C: the batch runs `min rem 62` steps, on the low 64 bits of `f` and `g` as signed words, starting from the identity matrix.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vIvA3fc : List BInstr :=
  [.alu .add a0 x0 (24 : Fin 32)]
theorem p2vIvA3fc_end : blockEnd p256VerifyPrehashCode 0x3FC p2vIvA3fc = some 0x3FE := by
  simp only [p2vIvA3fc]
  rw [blockEnd, p2v_at_3fc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvA406 : List BInstr :=
  [.alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x101]
theorem p2vIvA406_end : blockEnd p256VerifyPrehashCode 0x406 p2vIvA406 = some 0x410 := by
  simp only [p2vIvA406]
  rw [blockEnd, p2v_at_406]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_408]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_40c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvA418 : List BInstr :=
  [.alu .add (20 : Fin 32) x0 a0, .alu .add (26 : Fin 32) x0 a1, .aluImm .add a0 sp 0x200]
theorem p2vIvA418_end : blockEnd p256VerifyPrehashCode 0x418 p2vIvA418 = some 0x41E := by
  simp only [p2vIvA418]
  rw [blockEnd, p2v_at_418]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_41a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_41c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvA426 : List BInstr :=
  [.aluImm .add (6 : Fin 32) x0 0x0, .aluImm .add (25 : Fin 32) x0 0x0, .aluImm .add (7 : Fin 32) x0 0x0, .aluImm .add a2 x0 0x0, .aluImm .add a6 x0 0x0, .aluImm .add (17 : Fin 32) x0 0x0, .aluImm .add (30 : Fin 32) x0 0x1, .aluImm .add (9 : Fin 32) x0 0x1, .alu .add (5 : Fin 32) x0 (18 : Fin 32)]
theorem p2vIvA426_end : blockEnd p256VerifyPrehashCode 0x426 p2vIvA426 = some 0x438 := by
  simp only [p2vIvA426]
  rw [blockEnd, p2v_at_426]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_428]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_42a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_42c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_42e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_430]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_432]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_434]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_436]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_iva {B dlo dhi rem : Word} {fs gs ds es : BitVec 8} {qx qy qz rv sv zv fv gv dv ev : Nat} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0x3F8 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1)
    (g0_9 : reg n0 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755)
    (g0_19 : reg n0 (19 : Fin 32) = dlo)
    (g0_21 : reg n0 (21 : Fin 32) = dhi)
    (g0_22 : reg n0 (22 : Fin 32) = BitVec.ofNat 32 0x1)
    (g0_23 : reg n0 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4)
    (g0_24 : reg n0 (24 : Fin 32) = rem)
    (g0_26 : reg n0 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920)
    (g0_27 : reg n0 (27 : Fin 32) = BitVec.ofNat 32 0x7)
    (a0_120 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx)
    (a0_140 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy)
    (a0_160 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz)
    (a0_180 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv)
    (a0_1a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv)
    (a0_1c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv)
    (a0_200 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv)
    (a0_900 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv)
    (a0_980 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev)
    (a0_fe4 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv)
    (b0_220 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs)
    (b0_920 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs)
    (b0_9a0 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es)
    (b0_1004 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds)
    (IC0 : P2vIvCode M0)
    (hrem : rem ≠ 0)
    (hfs : fs.toNat ≤ 1)
    (hgs : gs.toNat ≤ 1) :
    (¬ (True) ∧ P2vRet B v n0 0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0x43C (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (5 : Fin 32) = (if (rem).toNat < 62 then rem else 62) ∧
        reg n' (6 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (7 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg n' a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) ∧
        reg n' a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) ∧
        reg n' a2 = BitVec.ofNat 32 0x0 ∧
        reg n' a6 = BitVec.ofNat 32 0x0 ∧
        reg n' a7 = BitVec.ofNat 32 0x0 ∧
        reg n' (18 : Fin 32) = (if (rem).toNat < 62 then rem else 62) ∧
        reg n' (19 : Fin 32) = dlo ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) ∧
        reg n' (21 : Fin 32) = dhi ∧
        reg n' (22 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg n' (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 ∧
        reg n' (24 : Fin 32) = rem ∧
        reg n' (25 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (26 : Fin 32) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) ∧
        reg n' (27 : Fin 32) = BitVec.ofNat 32 0x7 ∧
        reg n' (30 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv ∧
        P2vKeepL B n0.mem n'.mem [(0x50, 0x4), (0x54, 0x4)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x3F8: sw
  obtain ⟨n1, d1, s1, fr1, K1, W1, rg1⟩ := p2v_sw F E0 s0 p2v_at_3f8 (off' := 0x3FA) (c := 0x50)
    (by decide) (by rw [g0_2]; p2v_addr) (by decide) (by decide)
  have t1 : Steps n0 n1 := t0.trans d1
  have fR1 : ∀ x, P2vR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : P2vCode n1.mem := E0.fr F fr1
  have V1 : P2vSaves B n1.mem v := V0.keep K1 (by decide)
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [rg1 sp, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg1 (3 : Fin 32), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg1 (4 : Fin 32), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [rg1 (8 : Fin 32), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [rg1 (9 : Fin 32), g0_9]
  have g1_19 : reg n1 (19 : Fin 32) = dlo := by rw [rg1 (19 : Fin 32), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = dhi := by rw [rg1 (21 : Fin 32), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg1 (22 : Fin 32), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg1 (23 : Fin 32), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = rem := by rw [rg1 (24 : Fin 32), g0_24]
  have g1_26 : reg n1 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg1 (26 : Fin 32), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg1 (27 : Fin 32), g0_27]
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [(0x50, 0x4)] := (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem []).trans K1.toL
  have b1_220 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K1.b8 (by decide) (by decide)).trans b0_220
  have b1_920 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K1.b8 (by decide) (by decide)).trans b0_920
  have b1_9a0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K1.b8 (by decide) (by decide)).trans b0_9a0
  have b1_1004 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K1.b8 (by decide) (by decide)).trans b0_1004
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [W1, g0_9]
  have a1_120 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K1.acc (by decide) (by decide)).trans a0_120
  have a1_140 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K1.acc (by decide) (by decide)).trans a0_140
  have a1_160 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K1.acc (by decide) (by decide)).trans a0_160
  have a1_180 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K1.acc (by decide) (by decide)).trans a0_180
  have a1_1a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K1.acc (by decide) (by decide)).trans a0_1a0
  have a1_1c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K1.acc (by decide) (by decide)).trans a0_1c0
  have a1_200 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K1.acc (by decide) (by decide)).trans a0_200
  have a1_900 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K1.acc (by decide) (by decide)).trans a0_900
  have a1_980 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K1.acc (by decide) (by decide)).trans a0_980
  have a1_fe4 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K1.acc (by decide) (by decide)).trans a0_fe4
  -- 0x3FA: sw
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := p2v_sw F E1 s1 p2v_at_3fa (off' := 0x3FC) (c := 0x54)
    (by decide) (by rw [g1_2]; p2v_addr) (by decide) (by decide)
  have t2 : Steps n0 n2 := t1.trans d2
  have fR2 : ∀ x, P2vR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : P2vCode n2.mem := E1.fr F fr2
  have V2 : P2vSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rg2 sp, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg2 (3 : Fin 32), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg2 (4 : Fin 32), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [rg2 (8 : Fin 32), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [rg2 (9 : Fin 32), g1_9]
  have g2_19 : reg n2 (19 : Fin 32) = dlo := by rw [rg2 (19 : Fin 32), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = dhi := by rw [rg2 (21 : Fin 32), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg2 (22 : Fin 32), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg2 (23 : Fin 32), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = rem := by rw [rg2 (24 : Fin 32), g1_24]
  have g2_26 : reg n2 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg2 (26 : Fin 32), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg2 (27 : Fin 32), g1_27]
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [(0x50, 0x4), (0x54, 0x4)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K2.w32 (by decide) (by decide)).trans w1_50
  have b2_220 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K2.b8 (by decide) (by decide)).trans b1_220
  have b2_920 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K2.b8 (by decide) (by decide)).trans b1_920
  have b2_9a0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K2.b8 (by decide) (by decide)).trans b1_9a0
  have b2_1004 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K2.b8 (by decide) (by decide)).trans b1_1004
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [W2, g1_8]
  have a2_120 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K2.acc (by decide) (by decide)).trans a1_120
  have a2_140 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K2.acc (by decide) (by decide)).trans a1_140
  have a2_160 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K2.acc (by decide) (by decide)).trans a1_160
  have a2_180 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K2.acc (by decide) (by decide)).trans a1_180
  have a2_1a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K2.acc (by decide) (by decide)).trans a1_1a0
  have a2_1c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K2.acc (by decide) (by decide)).trans a1_1c0
  have a2_200 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K2.acc (by decide) (by decide)).trans a1_200
  have a2_900 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K2.acc (by decide) (by decide)).trans a1_900
  have a2_980 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K2.acc (by decide) (by decide)).trans a1_980
  have a2_fe4 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K2.acc (by decide) (by decide)).trans a1_fe4
  clear a1_fe4 a1_980 a1_900 a1_200 a1_1c0 a1_1a0 a1_180 a1_160 a1_140 a1_120 w1_50 b1_1004 b1_9a0 b1_920 b1_220 g1_27 g1_26 g1_24 g1_23 g1_22 g1_21 g1_19 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 rg1 W1 K1 fr1 s1 d1 g0_4 g0_3 fR0 t0
  -- 0x3FC
  obtain ⟨n3, c3, u3⟩ := s2.block p2vIvA3fc E2.self p2vIvA3fc_end
    ⟨trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem P2V n3 0x3FE (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock p2vIvA3fc (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have fr3 : ∀ x, P2vR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans c3
  have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : P2vCode n3.mem := E2.fr F fr3
  have V3 : P2vSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by
    rw [rb3, runBlock_reg _ _ _ sp s2.zero (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (3 : Fin 32) s2.zero (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (4 : Fin 32) s2.zero (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb3, runBlock_reg _ _ _ (8 : Fin 32) s2.zero (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [rb3, runBlock_reg _ _ _ (9 : Fin 32) s2.zero (by decide), g2_9]
  have g3_19 : reg n3 (19 : Fin 32) = dlo := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = dhi := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb3, runBlock_reg _ _ _ (22 : Fin 32) s2.zero (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb3, runBlock_reg _ _ _ (23 : Fin 32) s2.zero (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = rem := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_26 : reg n3 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_10 : reg n3 a0 = rem := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vIvA3fc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_9, g2_19, g2_21, g2_22, g2_23, g2_24, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0x50, 0x4), (0x54, 0x4)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m3]; exact w2_50
  have w3_54 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m3]; exact w2_54
  have b3_220 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m3]; exact b2_220
  have b3_920 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m3]; exact b2_920
  have b3_9a0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m3]; exact b2_9a0
  have b3_1004 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m3]; exact b2_1004
  have a3_120 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m3]; exact a2_120
  have a3_140 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m3]; exact a2_140
  have a3_160 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m3]; exact a2_160
  have a3_180 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m3]; exact a2_180
  have a3_1a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m3]; exact a2_1a0
  have a3_1c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m3]; exact a2_1c0
  have a3_200 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m3]; exact a2_200
  have a3_900 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m3]; exact a2_900
  have a3_980 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m3]; exact a2_980
  have a3_fe4 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m3]; exact a2_fe4
  clear a2_fe4 a2_980 a2_900 a2_200 a2_1c0 a2_1a0 a2_180 a2_160 a2_140 a2_120 w2_54 b2_1004 b2_9a0 b2_920 b2_220 w2_50 g2_27 g2_26 g2_24 g2_23 g2_22 g2_21 g2_19 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 rg2 W2 K2 fr2 s2 d2
  -- 0x3FE: p2v_uminF
  obtain ⟨n4, c4, s4, sp4, rk4, a0_4, K4, fr4⟩ := p2v_uminF 
    F E3 (IC0.p2v F fR3) s3 p2v_at_3fe p2v_at_402 (by decide) (by decide) g3_2 g3_10
  have t4 : Steps n0 n4 := t3.trans c4
  have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : P2vCode n4.mem := E3.fr F fr4
  have V4 : P2vSaves B n4.mem v := V3.keepL K4 (by decide)
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk4 (3 : Fin 32) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk4 (4 : Fin 32) (by decide), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [rk4 (8 : Fin 32) (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [rk4 (9 : Fin 32) (by decide), g3_9]
  have g4_19 : reg n4 (19 : Fin 32) = dlo := by rw [rk4 (19 : Fin 32) (by decide), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = dhi := by rw [rk4 (21 : Fin 32) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk4 (22 : Fin 32) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rk4 (23 : Fin 32) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = rem := by rw [rk4 (24 : Fin 32) (by decide), g3_24]
  have g4_26 : reg n4 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk4 (26 : Fin 32) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk4 (27 : Fin 32) (by decide), g3_27]
  have g4_2 : reg n4 sp = B + 0x21A0 := sp4
  have g4_10 : reg n4 a0 = (if (rem).toNat < 62 then rem else 62) := a0_4
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0x50, 0x4), (0x54, 0x4)] := keep_kk3.trans K4
  clear keep_kk3
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K4.w32 (by decide) (by decide)).trans w3_50
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K4.w32 (by decide) (by decide)).trans w3_54
  have b4_220 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K4.b8 (by decide) (by decide)).trans b3_220
  have b4_920 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K4.b8 (by decide) (by decide)).trans b3_920
  have b4_9a0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K4.b8 (by decide) (by decide)).trans b3_9a0
  have b4_1004 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K4.b8 (by decide) (by decide)).trans b3_1004
  have a4_120 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K4.acc (by decide) (by decide)).trans a3_120
  have a4_140 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K4.acc (by decide) (by decide)).trans a3_140
  have a4_160 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K4.acc (by decide) (by decide)).trans a3_160
  have a4_180 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K4.acc (by decide) (by decide)).trans a3_180
  have a4_1a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K4.acc (by decide) (by decide)).trans a3_1a0
  have a4_1c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K4.acc (by decide) (by decide)).trans a3_1c0
  have a4_200 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K4.acc (by decide) (by decide)).trans a3_200
  have a4_900 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K4.acc (by decide) (by decide)).trans a3_900
  have a4_980 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K4.acc (by decide) (by decide)).trans a3_980
  have a4_fe4 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K4.acc (by decide) (by decide)).trans a3_fe4
  clear a3_fe4 a3_980 a3_900 a3_200 a3_1c0 a3_1a0 a3_180 a3_160 a3_140 a3_120 b3_1004 b3_9a0 b3_920 b3_220 w3_54 w3_50 g3_10 g3_27 g3_26 g3_24 g3_23 g3_22 g3_21 g3_19 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  -- 0x406
  obtain ⟨n5, c5, u5⟩ := s4.block p2vIvA406 E4.self p2vIvA406_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem P2V n5 0x410 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock p2vIvA406 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb5, runBlock_reg _ _ _ (8 : Fin 32) s4.zero (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_19 : reg n5 (19 : Fin 32) = dlo := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = dhi := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = rem := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_26 : reg n5 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vIvA406, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_10, g4_19, g4_21, g4_22, g4_23, g4_24, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g5_18 : reg n5 (18 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vIvA406, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_10, g4_19, g4_21, g4_22, g4_23, g4_24, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0x50, 0x4), (0x54, 0x4)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m5]; exact w4_50
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m5]; exact w4_54
  have b5_220 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m5]; exact b4_220
  have b5_920 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m5]; exact b4_920
  have b5_9a0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m5]; exact b4_9a0
  have b5_1004 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m5]; exact b4_1004
  have a5_120 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m5]; exact a4_120
  have a5_140 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m5]; exact a4_140
  have a5_160 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m5]; exact a4_160
  have a5_180 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m5]; exact a4_180
  have a5_1a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m5]; exact a4_1a0
  have a5_1c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m5]; exact a4_1c0
  have a5_200 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m5]; exact a4_200
  have a5_900 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m5]; exact a4_900
  have a5_980 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m5]; exact a4_980
  have a5_fe4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m5]; exact a4_fe4
  clear a4_fe4 a4_980 a4_900 a4_200 a4_1c0 a4_1a0 a4_180 a4_160 a4_140 a4_120 b4_1004 b4_9a0 b4_920 b4_220 w4_54 w4_50 g4_10 g4_2 g4_27 g4_26 g4_24 g4_23 g4_22 g4_21 g4_19 g4_9 g4_8 g4_4 g4_3 V4 E4 fR4 t4 fr4 K4 a0_4 rk4 sp4 s4 c4
  -- 0x410: p2v_low8F
  obtain ⟨n6, c6, s6, sp6, rk6, L6, K6, fr6⟩ := p2v_low8F (oc := 0x900)
    F E5 (IC0.p2v F fR5) s5 p2v_at_410 p2v_at_414 (by decide) (by decide) g5_2
    g5_10 (by decide) (by decide) (by rw [show 0x900 + 0x20 = 0x920 from rfl, b5_920]; exact hfs)
  rw [show 0x900 + 0x20 = 0x920 from rfl, b5_920, acc2_of8 a5_900] at L6
  obtain ⟨e0_6, e1_6⟩ := w64_split L6
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.keepL K6 (by decide)
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk6 (3 : Fin 32) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk6 (4 : Fin 32) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [rk6 (8 : Fin 32) (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [rk6 (9 : Fin 32) (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [rk6 (18 : Fin 32) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = dlo := by rw [rk6 (19 : Fin 32) (by decide), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = dhi := by rw [rk6 (21 : Fin 32) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk6 (22 : Fin 32) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rk6 (23 : Fin 32) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = rem := by rw [rk6 (24 : Fin 32) (by decide), g5_24]
  have g6_26 : reg n6 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk6 (26 : Fin 32) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk6 (27 : Fin 32) (by decide), g5_27]
  have g6_2 : reg n6 sp = B + 0x21A0 := sp6
  have g6_10 : reg n6 a0 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := e0_6
  have g6_11 : reg n6 a1 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := e1_6
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0x50, 0x4), (0x54, 0x4)] := keep_kk5.trans K6
  clear keep_kk5
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K6.w32 (by decide) (by decide)).trans w5_50
  have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K6.w32 (by decide) (by decide)).trans w5_54
  have b6_220 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K6.b8 (by decide) (by decide)).trans b5_220
  have b6_920 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K6.b8 (by decide) (by decide)).trans b5_920
  have b6_9a0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K6.b8 (by decide) (by decide)).trans b5_9a0
  have b6_1004 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K6.b8 (by decide) (by decide)).trans b5_1004
  have a6_120 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K6.acc (by decide) (by decide)).trans a5_120
  have a6_140 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K6.acc (by decide) (by decide)).trans a5_140
  have a6_160 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K6.acc (by decide) (by decide)).trans a5_160
  have a6_180 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K6.acc (by decide) (by decide)).trans a5_180
  have a6_1a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K6.acc (by decide) (by decide)).trans a5_1a0
  have a6_1c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K6.acc (by decide) (by decide)).trans a5_1c0
  have a6_200 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K6.acc (by decide) (by decide)).trans a5_200
  have a6_900 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K6.acc (by decide) (by decide)).trans a5_900
  have a6_980 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K6.acc (by decide) (by decide)).trans a5_980
  have a6_fe4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K6.acc (by decide) (by decide)).trans a5_fe4
  clear a5_fe4 a5_980 a5_900 a5_200 a5_1c0 a5_1a0 a5_180 a5_160 a5_140 a5_120 b5_1004 b5_9a0 b5_920 b5_220 w5_54 w5_50 g5_18 g5_10 g5_27 g5_26 g5_24 g5_23 g5_22 g5_21 g5_19 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x418
  obtain ⟨n7, c7, u7⟩ := s6.block p2vIvA418 E6.self p2vIvA418_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem P2V n7 0x41E (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock p2vIvA418 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have fr7 : ∀ x, P2vR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : P2vCode n7.mem := E6.fr F fr7
  have V7 : P2vSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by
    rw [rb7, runBlock_reg _ _ _ sp s6.zero (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb7, runBlock_reg _ _ _ (3 : Fin 32) s6.zero (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb7, runBlock_reg _ _ _ (4 : Fin 32) s6.zero (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb7, runBlock_reg _ _ _ (8 : Fin 32) s6.zero (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
  have g7_11 : reg n7 a1 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by
    rw [rb7, runBlock_reg _ _ _ a1 s6.zero (by decide), g6_11]
  have g7_18 : reg n7 (18 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = dlo := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = dhi := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = rem := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_27 : reg n7 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vIvA418, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_11, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g7_20 : reg n7 (20 : Fin 32) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vIvA418, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_11, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g7_26 : reg n7 (26 : Fin 32) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vIvA418, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_11, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0x50, 0x4), (0x54, 0x4)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m7]; exact w6_50
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m7]; exact w6_54
  have b7_220 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m7]; exact b6_220
  have b7_920 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m7]; exact b6_920
  have b7_9a0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m7]; exact b6_9a0
  have b7_1004 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m7]; exact b6_1004
  have a7_120 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m7]; exact a6_120
  have a7_140 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m7]; exact a6_140
  have a7_160 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m7]; exact a6_160
  have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m7]; exact a6_180
  have a7_1a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m7]; exact a6_1a0
  have a7_1c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m7]; exact a6_1c0
  have a7_200 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m7]; exact a6_200
  have a7_900 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m7]; exact a6_900
  have a7_980 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m7]; exact a6_980
  have a7_fe4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m7]; exact a6_fe4
  clear a6_fe4 a6_980 a6_900 a6_200 a6_1c0 a6_1a0 a6_180 a6_160 a6_140 a6_120 b6_1004 b6_9a0 b6_920 b6_220 w6_54 w6_50 g6_11 g6_10 g6_2 g6_27 g6_26 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 V6 E6 fR6 t6 e1_6 e0_6 fr6 K6 L6 rk6 sp6 s6 c6
  -- 0x41E: p2v_low8F
  obtain ⟨n8, c8, s8, sp8, rk8, L8, K8, fr8⟩ := p2v_low8F (oc := 0x200)
    F E7 (IC0.p2v F fR7) s7 p2v_at_41e p2v_at_422 (by decide) (by decide) g7_2
    g7_10 (by decide) (by decide) (by rw [show 0x200 + 0x20 = 0x220 from rfl, b7_220]; exact hgs)
  rw [show 0x200 + 0x20 = 0x220 from rfl, b7_220, acc2_of8 a7_200] at L8
  obtain ⟨e0_8, e1_8⟩ := w64_split L8
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, P2vR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : P2vCode n8.mem := E7.fr F fr8
  have V8 : P2vSaves B n8.mem v := V7.keepL K8 (by decide)
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk8 (3 : Fin 32) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk8 (4 : Fin 32) (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [rk8 (8 : Fin 32) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [rk8 (9 : Fin 32) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [rk8 (18 : Fin 32) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = dlo := by rw [rk8 (19 : Fin 32) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by rw [rk8 (20 : Fin 32) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = dhi := by rw [rk8 (21 : Fin 32) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk8 (22 : Fin 32) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rk8 (23 : Fin 32) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = rem := by rw [rk8 (24 : Fin 32) (by decide), g7_24]
  have g8_26 : reg n8 (26 : Fin 32) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by rw [rk8 (26 : Fin 32) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk8 (27 : Fin 32) (by decide), g7_27]
  have g8_2 : reg n8 sp = B + 0x21A0 := sp8
  have g8_10 : reg n8 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := e0_8
  have g8_11 : reg n8 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := e1_8
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0x50, 0x4), (0x54, 0x4)] := keep_kk7.trans K8
  clear keep_kk7
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K8.w32 (by decide) (by decide)).trans w7_50
  have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K8.w32 (by decide) (by decide)).trans w7_54
  have b8_220 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K8.b8 (by decide) (by decide)).trans b7_220
  have b8_920 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K8.b8 (by decide) (by decide)).trans b7_920
  have b8_9a0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K8.b8 (by decide) (by decide)).trans b7_9a0
  have b8_1004 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K8.b8 (by decide) (by decide)).trans b7_1004
  have a8_120 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K8.acc (by decide) (by decide)).trans a7_120
  have a8_140 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K8.acc (by decide) (by decide)).trans a7_140
  have a8_160 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K8.acc (by decide) (by decide)).trans a7_160
  have a8_180 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K8.acc (by decide) (by decide)).trans a7_180
  have a8_1a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K8.acc (by decide) (by decide)).trans a7_1a0
  have a8_1c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K8.acc (by decide) (by decide)).trans a7_1c0
  have a8_200 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K8.acc (by decide) (by decide)).trans a7_200
  have a8_900 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K8.acc (by decide) (by decide)).trans a7_900
  have a8_980 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K8.acc (by decide) (by decide)).trans a7_980
  have a8_fe4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K8.acc (by decide) (by decide)).trans a7_fe4
  clear a7_fe4 a7_980 a7_900 a7_200 a7_1c0 a7_1a0 a7_180 a7_160 a7_140 a7_120 b7_1004 b7_9a0 b7_920 b7_220 w7_54 w7_50 g7_26 g7_20 g7_10 g7_27 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_11 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x426
  obtain ⟨n9, c9, u9⟩ := s8.block p2vIvA426 E8.self p2vIvA426_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem P2V n9 0x438 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock p2vIvA426 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
  have g9_10 : reg n9 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by
    rw [rb9, runBlock_reg _ _ _ a0 s8.zero (by decide), g8_10]
  have g9_11 : reg n9 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by
    rw [rb9, runBlock_reg _ _ _ a1 s8.zero (by decide), g8_11]
  have g9_18 : reg n9 (18 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = dlo := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = dhi := by
    rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb9, runBlock_reg _ _ _ (22 : Fin 32) s8.zero (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = rem := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_26 : reg n9 (26 : Fin 32) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_5 : reg n9 (5 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vIvA426, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_6 : reg n9 (6 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vIvA426, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_7 : reg n9 (7 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vIvA426, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_9 : reg n9 (9 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vIvA426, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_12 : reg n9 a2 = BitVec.ofNat 32 0x0 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vIvA426, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_16 : reg n9 a6 = BitVec.ofNat 32 0x0 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vIvA426, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_17 : reg n9 a7 = BitVec.ofNat 32 0x0 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vIvA426, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_25 : reg n9 (25 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vIvA426, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_30 : reg n9 (30 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vIvA426, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0x50, 0x4), (0x54, 0x4)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m9]; exact w8_50
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m9]; exact w8_54
  have b9_220 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m9]; exact b8_220
  have b9_920 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m9]; exact b8_920
  have b9_9a0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m9]; exact b8_9a0
  have b9_1004 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m9]; exact b8_1004
  have a9_120 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m9]; exact a8_120
  have a9_140 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m9]; exact a8_140
  have a9_160 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m9]; exact a8_160
  have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m9]; exact a8_180
  have a9_1a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m9]; exact a8_1a0
  have a9_1c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m9]; exact a8_1c0
  have a9_200 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m9]; exact a8_200
  have a9_900 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m9]; exact a8_900
  have a9_980 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m9]; exact a8_980
  have a9_fe4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m9]; exact a8_fe4
  clear a8_fe4 a8_980 a8_900 a8_200 a8_1c0 a8_1a0 a8_180 a8_160 a8_140 a8_120 b8_1004 b8_9a0 b8_920 b8_220 w8_54 w8_50 g8_11 g8_10 g8_2 g8_27 g8_26 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 V8 E8 fR8 t8 e1_8 e0_8 fr8 K8 L8 rk8 sp8 s8 c8
  -- 0x438: branch, not taken
  obtain ⟨n10, d10, u10⟩ := s9.notTaken E9.self 0x43C p2v_at_438
    (by decide) (by rw [g9_18, s9.zero]; exact br_beq_f (umin_ne0 hrem))
  have s10 : St n10.mem P2V n10 0x43C (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, P2vR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : P2vCode n10.mem := E9.fr F fr10
  have V10 : P2vSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
  have g10_5 : reg n10 (5 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [u10.regs, g9_5]
  have g10_6 : reg n10 (6 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u10.regs, g9_6]
  have g10_7 : reg n10 (7 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u10.regs, g9_7]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [u10.regs, g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u10.regs, g9_9]
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by rw [u10.regs, g9_10]
  have g10_11 : reg n10 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by rw [u10.regs, g9_11]
  have g10_12 : reg n10 a2 = BitVec.ofNat 32 0x0 := by rw [u10.regs, g9_12]
  have g10_16 : reg n10 a6 = BitVec.ofNat 32 0x0 := by rw [u10.regs, g9_16]
  have g10_17 : reg n10 a7 = BitVec.ofNat 32 0x0 := by rw [u10.regs, g9_17]
  have g10_18 : reg n10 (18 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [u10.regs, g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = dlo := by rw [u10.regs, g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by rw [u10.regs, g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = dhi := by rw [u10.regs, g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u10.regs, g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [u10.regs, g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = rem := by rw [u10.regs, g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u10.regs, g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by rw [u10.regs, g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u10.regs, g9_27]
  have g10_30 : reg n10 (30 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u10.regs, g9_30]
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0x50, 0x4), (0x54, 0x4)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m10]; exact w9_50
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m10]; exact w9_54
  have b10_220 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m10]; exact b9_220
  have b10_920 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m10]; exact b9_920
  have b10_9a0 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m10]; exact b9_9a0
  have b10_1004 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m10]; exact b9_1004
  have a10_120 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m10]; exact a9_120
  have a10_140 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m10]; exact a9_140
  have a10_160 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m10]; exact a9_160
  have a10_180 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m10]; exact a9_180
  have a10_1a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m10]; exact a9_1a0
  have a10_1c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m10]; exact a9_1c0
  have a10_200 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m10]; exact a9_200
  have a10_900 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m10]; exact a9_900
  have a10_980 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m10]; exact a9_980
  have a10_fe4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m10]; exact a9_fe4
  clear a9_fe4 a9_980 a9_900 a9_200 a9_1c0 a9_1a0 a9_180 a9_160 a9_140 a9_120 b9_1004 b9_9a0 b9_920 b9_220 w9_54 w9_50 g9_30 g9_25 g9_17 g9_16 g9_12 g9_9 g9_7 g9_6 g9_5 g9_27 g9_26 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_11 g9_10 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  exact .inr ⟨n10, t10, s10, E10, V10, fR10, g10_2, g10_3, g10_4, g10_5, g10_6, g10_7, g10_8, g10_9, g10_10, g10_11, g10_12, g10_16, g10_17, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_25, g10_26, g10_27, g10_30, w10_50, w10_54, b10_220, b10_920, b10_9a0, b10_1004, a10_120, a10_140, a10_160, a10_180, a10_1a0, a10_1c0, a10_200, a10_900, a10_980, a10_fe4, keep_kk10.mono (by decide)⟩

end C3.RV32.P2v
