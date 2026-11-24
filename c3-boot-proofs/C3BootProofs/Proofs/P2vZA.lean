import C3BootProofs.Proofs.P2vZLib

/-!
# `p256VerifyPrehash`: the start of a batch of the inversion of `Z`

From the inversion's head at 0xBEE to the divstep loop at 0xC3C: the batch runs `min rem 62` steps, on the low 64 bits of `f` and `g` as signed words, starting from the identity matrix.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vZAbf0 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a4]
theorem p2vZAbf0_end : blockEnd p256VerifyPrehashCode 0xBF0 p2vZAbf0 = some 0xBF2 := by
  simp only [p2vZAbf0]
  rw [blockEnd, p2v_at_bf0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZAbfa : List BInstr :=
  [.alu .add (9 : Fin 32) x0 a0, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x781]
theorem p2vZAbfa_end : blockEnd p256VerifyPrehashCode 0xBFA p2vZAbfa = some 0xC04 := by
  simp only [p2vZAbfa]
  rw [blockEnd, p2v_at_bfa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_bfc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_c00]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZAc10 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x101]
theorem p2vZAc10_end : blockEnd p256VerifyPrehashCode 0xC10 p2vZAc10 = some 0xC18 := by
  simp only [p2vZAc10]
  rw [blockEnd, p2v_at_c10]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_c14]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZAc24 : List BInstr :=
  [.aluImm .add a3 x0 0x0]
theorem p2vZAc24_end : blockEnd p256VerifyPrehashCode 0xC24 p2vZAc24 = some 0xC26 := by
  simp only [p2vZAc24]
  rw [blockEnd, p2v_at_c24]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZAc28 : List BInstr :=
  [.aluImm .add (18 : Fin 32) x0 0x0, .aluImm .add (20 : Fin 32) x0 0x0, .aluImm .add (25 : Fin 32) x0 0x0, .aluImm .add (26 : Fin 32) x0 0x0, .aluImm .add (22 : Fin 32) x0 0x1, .aluImm .add (23 : Fin 32) x0 0x1]
theorem p2vZAc28_end : blockEnd p256VerifyPrehashCode 0xC28 p2vZAc28 = some 0xC34 := by
  simp only [p2vZAc28]
  rw [blockEnd, p2v_at_c28]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_c2a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_c2c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_c2e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_c30]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_c32]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZAc36 : List BInstr :=
  [.alu .add a4 x0 (9 : Fin 32)]
theorem p2vZAc36_end : blockEnd p256VerifyPrehashCode 0xC36 p2vZAc36 = some 0xC38 := by
  simp only [p2vZAc36]
  rw [blockEnd, p2v_at_c36]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_za {B dlo dhi rem nzw : Word} {fs gs ds es : BitVec 8} {rv X Y fv gv dv ev : Nat} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0xBEE (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = rem)
    (g0_14 : reg n0 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920)
    (g0_24 : reg n0 (24 : Fin 32) = dhi)
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo)
    (a0_180 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv)
    (a0_200 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv)
    (a0_900 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv)
    (a0_980 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)
    (a0_f80 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv)
    (a0_fe4 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev)
    (a0_1338 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X)
    (a0_1358 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y)
    (b0_220 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds)
    (b0_920 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs)
    (b0_fa0 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs)
    (b0_1004 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es)
    (IC0 : P2vIvCode M0)
    (hrem : rem ≠ 0)
    (hfs : fs.toNat ≤ 1)
    (hgs : gs.toNat ≤ 1) :
    (¬ (True) ∧ P2vRet B v n0 0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0xC3C (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
        reg n' (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) ∧
        reg n' a3 = BitVec.ofNat 32 0x0 ∧
        reg n' a4 = (if (rem).toNat < 62 then rem else 62) ∧
        reg n' (18 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (22 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg n' (23 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg n' (24 : Fin 32) = dhi ∧
        reg n' (25 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (26 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = (if (rem).toNat < 62 then rem else 62) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x0 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y ∧
        P2vKeepL B n0.mem n'.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4), (0x44, 0x4), (0x4C, 0x4), (0x54, 0x4), (0x14, 0x4)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xBEE: sw
  obtain ⟨n1, d1, s1, fr1, K1, W1, rg1⟩ := p2v_sw F E0 s0 p2v_at_bee (off' := 0xBF0) (c := 0x18)
    (by decide) (by rw [g0_2]; p2v_addr) (by decide) (by decide)
  have t1 : Steps n0 n1 := t0.trans d1
  have fR1 : ∀ x, P2vR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : P2vCode n1.mem := E0.fr F fr1
  have V1 : P2vSaves B n1.mem v := V0.keep K1 (by decide)
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [rg1 sp, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg1 (3 : Fin 32), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg1 (4 : Fin 32), g0_4]
  have g1_10 : reg n1 a0 = rem := by rw [rg1 a0, g0_10]
  have g1_14 : reg n1 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg1 a4, g0_14]
  have g1_24 : reg n1 (24 : Fin 32) = dhi := by rw [rg1 (24 : Fin 32), g0_24]
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [(0x18, 0x4)] := (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem []).trans K1.toL
  have w1_10 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K1.w32 (by decide) (by decide)).trans w0_10
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K1.w32 (by decide) (by decide)).trans w0_40
  have b1_220 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K1.b8 (by decide) (by decide)).trans b0_220
  have b1_920 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K1.b8 (by decide) (by decide)).trans b0_920
  have b1_fa0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K1.b8 (by decide) (by decide)).trans b0_fa0
  have b1_1004 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K1.b8 (by decide) (by decide)).trans b0_1004
  have w1_18 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [W1, g0_10]
  have a1_180 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K1.acc (by decide) (by decide)).trans a0_180
  have a1_200 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K1.acc (by decide) (by decide)).trans a0_200
  have a1_900 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K1.acc (by decide) (by decide)).trans a0_900
  have a1_980 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K1.acc (by decide) (by decide)).trans a0_980
  have a1_f80 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K1.acc (by decide) (by decide)).trans a0_f80
  have a1_fe4 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K1.acc (by decide) (by decide)).trans a0_fe4
  have a1_1338 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K1.acc (by decide) (by decide)).trans a0_1338
  have a1_1358 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K1.acc (by decide) (by decide)).trans a0_1358
  -- 0xBF0
  obtain ⟨n2, c2, u2⟩ := s1.block p2vZAbf0 E1.self p2vZAbf0_end
    ⟨trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem P2V n2 0xBF2 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock p2vZAbf0 (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
  have fr2 : ∀ x, P2vR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, P2vR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : P2vCode n2.mem := E1.fr F fr2
  have V2 : P2vSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by
    rw [rb2, runBlock_reg _ _ _ sp s1.zero (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb2, runBlock_reg _ _ _ (3 : Fin 32) s1.zero (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb2, runBlock_reg _ _ _ (4 : Fin 32) s1.zero (by decide), g1_4]
  have g2_10 : reg n2 a0 = rem := by
    rw [rb2, runBlock_reg _ _ _ a0 s1.zero (by decide), g1_10]
  have g2_14 : reg n2 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb2, runBlock_reg _ _ _ a4 s1.zero (by decide), g1_14]
  have g2_24 : reg n2 (24 : Fin 32) = dhi := by
    rw [rb2, runBlock_reg _ _ _ (24 : Fin 32) s1.zero (by decide), g1_24]
  have g2_8 : reg n2 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vZAbf0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_10, g1_14, g1_24, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [(0x18, 0x4)] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_10 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m2]; exact w1_10
  have w2_18 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m2]; exact w1_18
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m2]; exact w1_40
  have b2_220 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m2]; exact b1_220
  have b2_920 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m2]; exact b1_920
  have b2_fa0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m2]; exact b1_fa0
  have b2_1004 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m2]; exact b1_1004
  have a2_180 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m2]; exact a1_180
  have a2_200 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m2]; exact a1_200
  have a2_900 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m2]; exact a1_900
  have a2_980 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m2]; exact a1_980
  have a2_f80 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m2]; exact a1_f80
  have a2_fe4 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m2]; exact a1_fe4
  have a2_1338 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m2]; exact a1_1338
  have a2_1358 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m2]; exact a1_1358
  clear a1_1358 a1_1338 a1_fe4 a1_f80 a1_980 a1_900 a1_200 a1_180 w1_18 b1_1004 b1_fa0 b1_920 b1_220 w1_40 w1_10 g1_24 g1_14 g1_10 g1_4 g1_3 g1_2 V1 E1 fR1 t1 rg1 W1 K1 fr1 s1 d1 g0_4 g0_3 fR0 t0
  -- 0xBF2: p2v_uminF
  obtain ⟨n3, c3, s3, sp3, rk3, a0_3, K3, fr3⟩ := p2v_uminF 
    F E2 (IC0.p2v F fR2) s2 p2v_at_bf2 p2v_at_bf6 (by decide) (by decide) g2_2 g2_10
  have t3 : Steps n0 n3 := t2.trans c3
  have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : P2vCode n3.mem := E2.fr F fr3
  have V3 : P2vSaves B n3.mem v := V2.keepL K3 (by decide)
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk3 (3 : Fin 32) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk3 (4 : Fin 32) (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk3 (8 : Fin 32) (by decide), g2_8]
  have g3_24 : reg n3 (24 : Fin 32) = dhi := by rw [rk3 (24 : Fin 32) (by decide), g2_24]
  have g3_2 : reg n3 sp = B + 0x21A0 := sp3
  have g3_10 : reg n3 a0 = (if (rem).toNat < 62 then rem else 62) := a0_3
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0x18, 0x4)] := keep_kk2.trans K3
  clear keep_kk2
  have w3_10 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K3.w32 (by decide) (by decide)).trans w2_10
  have w3_18 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K3.w32 (by decide) (by decide)).trans w2_18
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K3.w32 (by decide) (by decide)).trans w2_40
  have b3_220 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K3.b8 (by decide) (by decide)).trans b2_220
  have b3_920 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K3.b8 (by decide) (by decide)).trans b2_920
  have b3_fa0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K3.b8 (by decide) (by decide)).trans b2_fa0
  have b3_1004 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K3.b8 (by decide) (by decide)).trans b2_1004
  have a3_180 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K3.acc (by decide) (by decide)).trans a2_180
  have a3_200 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K3.acc (by decide) (by decide)).trans a2_200
  have a3_900 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K3.acc (by decide) (by decide)).trans a2_900
  have a3_980 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K3.acc (by decide) (by decide)).trans a2_980
  have a3_f80 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K3.acc (by decide) (by decide)).trans a2_f80
  have a3_fe4 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K3.acc (by decide) (by decide)).trans a2_fe4
  have a3_1338 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K3.acc (by decide) (by decide)).trans a2_1338
  have a3_1358 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K3.acc (by decide) (by decide)).trans a2_1358
  clear a2_1358 a2_1338 a2_fe4 a2_f80 a2_980 a2_900 a2_200 a2_180 b2_1004 b2_fa0 b2_920 b2_220 w2_40 w2_18 w2_10 g2_8 g2_24 g2_14 g2_10 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0xBFA
  obtain ⟨n4, c4, u4⟩ := s3.block p2vZAbfa E3.self p2vZAbfa_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem P2V n4 0xC04 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock p2vZAbfa (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_8 : reg n4 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb4, runBlock_reg _ _ _ (8 : Fin 32) s3.zero (by decide), g3_8]
  have g4_24 : reg n4 (24 : Fin 32) = dhi := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_9 : reg n4 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vZAbfa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_10, g3_24, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vZAbfa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_10, g3_24, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0x18, 0x4)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_10 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m4]; exact w3_10
  have w4_18 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m4]; exact w3_18
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m4]; exact w3_40
  have b4_220 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m4]; exact b3_220
  have b4_920 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m4]; exact b3_920
  have b4_fa0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m4]; exact b3_fa0
  have b4_1004 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m4]; exact b3_1004
  have a4_180 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m4]; exact a3_180
  have a4_200 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m4]; exact a3_200
  have a4_900 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m4]; exact a3_900
  have a4_980 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m4]; exact a3_980
  have a4_f80 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m4]; exact a3_f80
  have a4_fe4 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m4]; exact a3_fe4
  have a4_1338 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m4]; exact a3_1338
  have a4_1358 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m4]; exact a3_1358
  clear a3_1358 a3_1338 a3_fe4 a3_f80 a3_980 a3_900 a3_200 a3_180 b3_1004 b3_fa0 b3_920 b3_220 w3_40 w3_18 w3_10 g3_10 g3_2 g3_24 g3_8 g3_4 g3_3 V3 E3 fR3 t3 fr3 K3 a0_3 rk3 sp3 s3 c3
  -- 0xC04: p2v_low8F
  obtain ⟨n5, c5, s5, sp5, rk5, L5, K5, fr5⟩ := p2v_low8F (oc := 0xF80)
    F E4 (IC0.p2v F fR4) s4 p2v_at_c04 p2v_at_c08 (by decide) (by decide) g4_2
    g4_10 (by decide) (by decide) (by rw [show 0xF80 + 0x20 = 0xFA0 from rfl, b4_fa0]; exact hfs)
  rw [show 0xF80 + 0x20 = 0xFA0 from rfl, b4_fa0, acc2_of8 a4_f80] at L5
  obtain ⟨e0_5, e1_5⟩ := w64_split L5
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, P2vR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : P2vCode n5.mem := E4.fr F fr5
  have V5 : P2vSaves B n5.mem v := V4.keepL K5 (by decide)
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk5 (3 : Fin 32) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk5 (4 : Fin 32) (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk5 (8 : Fin 32) (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [rk5 (9 : Fin 32) (by decide), g4_9]
  have g5_24 : reg n5 (24 : Fin 32) = dhi := by rw [rk5 (24 : Fin 32) (by decide), g4_24]
  have g5_2 : reg n5 sp = B + 0x21A0 := sp5
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := e0_5
  have g5_11 : reg n5 a1 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := e1_5
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0x18, 0x4)] := keep_kk4.trans K5
  clear keep_kk4
  have w5_10 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K5.w32 (by decide) (by decide)).trans w4_10
  have w5_18 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K5.w32 (by decide) (by decide)).trans w4_18
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K5.w32 (by decide) (by decide)).trans w4_40
  have b5_220 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K5.b8 (by decide) (by decide)).trans b4_220
  have b5_920 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K5.b8 (by decide) (by decide)).trans b4_920
  have b5_fa0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K5.b8 (by decide) (by decide)).trans b4_fa0
  have b5_1004 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K5.b8 (by decide) (by decide)).trans b4_1004
  have a5_180 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K5.acc (by decide) (by decide)).trans a4_180
  have a5_200 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K5.acc (by decide) (by decide)).trans a4_200
  have a5_900 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K5.acc (by decide) (by decide)).trans a4_900
  have a5_980 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K5.acc (by decide) (by decide)).trans a4_980
  have a5_f80 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K5.acc (by decide) (by decide)).trans a4_f80
  have a5_fe4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K5.acc (by decide) (by decide)).trans a4_fe4
  have a5_1338 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K5.acc (by decide) (by decide)).trans a4_1338
  have a5_1358 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K5.acc (by decide) (by decide)).trans a4_1358
  clear a4_1358 a4_1338 a4_fe4 a4_f80 a4_980 a4_900 a4_200 a4_180 b4_1004 b4_fa0 b4_920 b4_220 w4_40 w4_18 w4_10 g4_10 g4_9 g4_24 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0xC0C: sw
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := p2v_sw F E5 s5 p2v_at_c0c (off' := 0xC0E) (c := 0x50)
    (by decide) (by rw [g5_2]; p2v_addr) (by decide) (by decide)
  have t6 : Steps n0 n6 := t5.trans d6
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rg6 sp, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg6 (3 : Fin 32), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg6 (4 : Fin 32), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg6 (8 : Fin 32), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [rg6 (9 : Fin 32), g5_9]
  have g6_10 : reg n6 a0 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by rw [rg6 a0, g5_10]
  have g6_11 : reg n6 a1 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by rw [rg6 a1, g5_11]
  have g6_24 : reg n6 (24 : Fin 32) = dhi := by rw [rg6 (24 : Fin 32), g5_24]
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0x18, 0x4), (0x50, 0x4)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_10 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K6.w32 (by decide) (by decide)).trans w5_10
  have w6_18 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K6.w32 (by decide) (by decide)).trans w5_18
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K6.w32 (by decide) (by decide)).trans w5_40
  have b6_220 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K6.b8 (by decide) (by decide)).trans b5_220
  have b6_920 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K6.b8 (by decide) (by decide)).trans b5_920
  have b6_fa0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K6.b8 (by decide) (by decide)).trans b5_fa0
  have b6_1004 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K6.b8 (by decide) (by decide)).trans b5_1004
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by rw [W6, g5_10]
  have a6_180 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K6.acc (by decide) (by decide)).trans a5_180
  have a6_200 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K6.acc (by decide) (by decide)).trans a5_200
  have a6_900 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K6.acc (by decide) (by decide)).trans a5_900
  have a6_980 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K6.acc (by decide) (by decide)).trans a5_980
  have a6_f80 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K6.acc (by decide) (by decide)).trans a5_f80
  have a6_fe4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K6.acc (by decide) (by decide)).trans a5_fe4
  have a6_1338 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K6.acc (by decide) (by decide)).trans a5_1338
  have a6_1358 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K6.acc (by decide) (by decide)).trans a5_1358
  clear a5_1358 a5_1338 a5_fe4 a5_f80 a5_980 a5_900 a5_200 a5_180 b5_1004 b5_fa0 b5_920 b5_220 w5_40 w5_18 w5_10 g5_11 g5_10 g5_2 g5_24 g5_9 g5_8 g5_4 g5_3 V5 E5 fR5 t5 e1_5 e0_5 fr5 K5 L5 rk5 sp5 s5 c5
  -- 0xC0E: sw
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := p2v_sw F E6 s6 p2v_at_c0e (off' := 0xC10) (c := 0x48)
    (by decide) (by rw [g6_2]; p2v_addr) (by decide) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : P2vCode n7.mem := E6.fr F fr7
  have V7 : P2vSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg7 (8 : Fin 32), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [rg7 (9 : Fin 32), g6_9]
  have g7_10 : reg n7 a0 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by rw [rg7 a0, g6_10]
  have g7_11 : reg n7 a1 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by rw [rg7 a1, g6_11]
  have g7_24 : reg n7 (24 : Fin 32) = dhi := by rw [rg7 (24 : Fin 32), g6_24]
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_10 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K7.w32 (by decide) (by decide)).trans w6_10
  have w7_18 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K7.w32 (by decide) (by decide)).trans w6_18
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K7.w32 (by decide) (by decide)).trans w6_40
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := (K7.w32 (by decide) (by decide)).trans w6_50
  have b7_220 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K7.b8 (by decide) (by decide)).trans b6_220
  have b7_920 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K7.b8 (by decide) (by decide)).trans b6_920
  have b7_fa0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K7.b8 (by decide) (by decide)).trans b6_fa0
  have b7_1004 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K7.b8 (by decide) (by decide)).trans b6_1004
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by rw [W7, g6_11]
  have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K7.acc (by decide) (by decide)).trans a6_180
  have a7_200 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K7.acc (by decide) (by decide)).trans a6_200
  have a7_900 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K7.acc (by decide) (by decide)).trans a6_900
  have a7_980 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K7.acc (by decide) (by decide)).trans a6_980
  have a7_f80 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K7.acc (by decide) (by decide)).trans a6_f80
  have a7_fe4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K7.acc (by decide) (by decide)).trans a6_fe4
  have a7_1338 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K7.acc (by decide) (by decide)).trans a6_1338
  have a7_1358 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K7.acc (by decide) (by decide)).trans a6_1358
  clear a6_1358 a6_1338 a6_fe4 a6_f80 a6_980 a6_900 a6_200 a6_180 w6_50 b6_1004 b6_fa0 b6_920 b6_220 w6_40 w6_18 w6_10 g6_24 g6_11 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
  -- 0xC10
  obtain ⟨n8, c8, u8⟩ := s7.block p2vZAc10 E7.self p2vZAc10_end
    ⟨trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem P2V n8 0xC18 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock p2vZAc10 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_8 : reg n8 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb8, runBlock_reg _ _ _ (8 : Fin 32) s7.zero (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by
    rw [rb8, runBlock_reg _ _ _ (9 : Fin 32) s7.zero (by decide), g7_9]
  have g8_11 : reg n8 a1 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by
    rw [rb8, runBlock_reg _ _ _ a1 s7.zero (by decide), g7_11]
  have g8_24 : reg n8 (24 : Fin 32) = dhi := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vZAc10, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_11, g7_24, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_10 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m8]; exact w7_10
  have w8_18 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m8]; exact w7_18
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m8]; exact w7_40
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by rw [m8]; exact w7_48
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by rw [m8]; exact w7_50
  have b8_220 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m8]; exact b7_220
  have b8_920 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m8]; exact b7_920
  have b8_fa0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m8]; exact b7_fa0
  have b8_1004 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m8]; exact b7_1004
  have a8_180 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m8]; exact a7_180
  have a8_200 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m8]; exact a7_200
  have a8_900 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m8]; exact a7_900
  have a8_980 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m8]; exact a7_980
  have a8_f80 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m8]; exact a7_f80
  have a8_fe4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m8]; exact a7_fe4
  have a8_1338 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m8]; exact a7_1338
  have a8_1358 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m8]; exact a7_1358
  clear a7_1358 a7_1338 a7_fe4 a7_f80 a7_980 a7_900 a7_200 a7_180 w7_48 b7_1004 b7_fa0 b7_920 b7_220 w7_50 w7_40 w7_18 w7_10 g7_24 g7_11 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0xC18: p2v_low8F
  obtain ⟨n9, c9, s9, sp9, rk9, L9, K9, fr9⟩ := p2v_low8F (oc := 0x900)
    F E8 (IC0.p2v F fR8) s8 p2v_at_c18 p2v_at_c1c (by decide) (by decide) g8_2
    g8_10 (by decide) (by decide) (by rw [show 0x900 + 0x20 = 0x920 from rfl, b8_920]; exact hgs)
  rw [show 0x900 + 0x20 = 0x920 from rfl, b8_920, acc2_of8 a8_900] at L9
  obtain ⟨e0_9, e1_9⟩ := w64_split L9
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, P2vR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : P2vCode n9.mem := E8.fr F fr9
  have V9 : P2vSaves B n9.mem v := V8.keepL K9 (by decide)
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk9 (3 : Fin 32) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk9 (4 : Fin 32) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk9 (8 : Fin 32) (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [rk9 (9 : Fin 32) (by decide), g8_9]
  have g9_24 : reg n9 (24 : Fin 32) = dhi := by rw [rk9 (24 : Fin 32) (by decide), g8_24]
  have g9_2 : reg n9 sp = B + 0x21A0 := sp9
  have g9_10 : reg n9 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := e0_9
  have g9_11 : reg n9 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := e1_9
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4)] := keep_kk8.trans K9
  clear keep_kk8
  have w9_10 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K9.w32 (by decide) (by decide)).trans w8_10
  have w9_18 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K9.w32 (by decide) (by decide)).trans w8_18
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K9.w32 (by decide) (by decide)).trans w8_40
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := (K9.w32 (by decide) (by decide)).trans w8_48
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := (K9.w32 (by decide) (by decide)).trans w8_50
  have b9_220 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K9.b8 (by decide) (by decide)).trans b8_220
  have b9_920 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K9.b8 (by decide) (by decide)).trans b8_920
  have b9_fa0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K9.b8 (by decide) (by decide)).trans b8_fa0
  have b9_1004 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K9.b8 (by decide) (by decide)).trans b8_1004
  have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K9.acc (by decide) (by decide)).trans a8_180
  have a9_200 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K9.acc (by decide) (by decide)).trans a8_200
  have a9_900 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K9.acc (by decide) (by decide)).trans a8_900
  have a9_980 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K9.acc (by decide) (by decide)).trans a8_980
  have a9_f80 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K9.acc (by decide) (by decide)).trans a8_f80
  have a9_fe4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K9.acc (by decide) (by decide)).trans a8_fe4
  have a9_1338 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K9.acc (by decide) (by decide)).trans a8_1338
  have a9_1358 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K9.acc (by decide) (by decide)).trans a8_1358
  clear a8_1358 a8_1338 a8_fe4 a8_f80 a8_980 a8_900 a8_200 a8_180 b8_1004 b8_fa0 b8_920 b8_220 w8_50 w8_48 w8_40 w8_18 w8_10 g8_10 g8_24 g8_11 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0xC20: sw
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := p2v_sw F E9 s9 p2v_at_c20 (off' := 0xC22) (c := 0x44)
    (by decide) (by rw [g9_2]; p2v_addr) (by decide) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : P2vCode n10.mem := E9.fr F fr10
  have V10 : P2vSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg10 (8 : Fin 32), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [rg10 (9 : Fin 32), g9_9]
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by rw [rg10 a0, g9_10]
  have g10_11 : reg n10 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by rw [rg10 a1, g9_11]
  have g10_24 : reg n10 (24 : Fin 32) = dhi := by rw [rg10 (24 : Fin 32), g9_24]
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4), (0x44, 0x4)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_10 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K10.w32 (by decide) (by decide)).trans w9_10
  have w10_18 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K10.w32 (by decide) (by decide)).trans w9_18
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K10.w32 (by decide) (by decide)).trans w9_40
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := (K10.w32 (by decide) (by decide)).trans w9_48
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := (K10.w32 (by decide) (by decide)).trans w9_50
  have b10_220 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K10.b8 (by decide) (by decide)).trans b9_220
  have b10_920 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K10.b8 (by decide) (by decide)).trans b9_920
  have b10_fa0 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K10.b8 (by decide) (by decide)).trans b9_fa0
  have b10_1004 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K10.b8 (by decide) (by decide)).trans b9_1004
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by rw [W10, g9_10]
  have a10_180 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K10.acc (by decide) (by decide)).trans a9_180
  have a10_200 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K10.acc (by decide) (by decide)).trans a9_200
  have a10_900 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K10.acc (by decide) (by decide)).trans a9_900
  have a10_980 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K10.acc (by decide) (by decide)).trans a9_980
  have a10_f80 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K10.acc (by decide) (by decide)).trans a9_f80
  have a10_fe4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K10.acc (by decide) (by decide)).trans a9_fe4
  have a10_1338 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K10.acc (by decide) (by decide)).trans a9_1338
  have a10_1358 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K10.acc (by decide) (by decide)).trans a9_1358
  clear a9_1358 a9_1338 a9_fe4 a9_f80 a9_980 a9_900 a9_200 a9_180 b9_1004 b9_fa0 b9_920 b9_220 w9_50 w9_48 w9_40 w9_18 w9_10 g9_11 g9_10 g9_2 g9_24 g9_9 g9_8 g9_4 g9_3 V9 E9 fR9 t9 e1_9 e0_9 fr9 K9 L9 rk9 sp9 s9 c9
  -- 0xC22: sw
  obtain ⟨n11, d11, s11, fr11, K11, W11, rg11⟩ := p2v_sw F E10 s10 p2v_at_c22 (off' := 0xC24) (c := 0x4C)
    (by decide) (by rw [g10_2]; p2v_addr) (by decide) (by decide)
  have t11 : Steps n0 n11 := t10.trans d11
  have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : P2vCode n11.mem := E10.fr F fr11
  have V11 : P2vSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rg11 sp, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg11 (3 : Fin 32), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg11 (4 : Fin 32), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg11 (8 : Fin 32), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [rg11 (9 : Fin 32), g10_9]
  have g11_10 : reg n11 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by rw [rg11 a0, g10_10]
  have g11_11 : reg n11 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by rw [rg11 a1, g10_11]
  have g11_24 : reg n11 (24 : Fin 32) = dhi := by rw [rg11 (24 : Fin 32), g10_24]
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4), (0x44, 0x4), (0x4C, 0x4)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have w11_10 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K11.w32 (by decide) (by decide)).trans w10_10
  have w11_18 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K11.w32 (by decide) (by decide)).trans w10_18
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K11.w32 (by decide) (by decide)).trans w10_40
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := (K11.w32 (by decide) (by decide)).trans w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := (K11.w32 (by decide) (by decide)).trans w10_48
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := (K11.w32 (by decide) (by decide)).trans w10_50
  have b11_220 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K11.b8 (by decide) (by decide)).trans b10_220
  have b11_920 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K11.b8 (by decide) (by decide)).trans b10_920
  have b11_fa0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K11.b8 (by decide) (by decide)).trans b10_fa0
  have b11_1004 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K11.b8 (by decide) (by decide)).trans b10_1004
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by rw [W11, g10_11]
  have a11_180 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K11.acc (by decide) (by decide)).trans a10_180
  have a11_200 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K11.acc (by decide) (by decide)).trans a10_200
  have a11_900 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K11.acc (by decide) (by decide)).trans a10_900
  have a11_980 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K11.acc (by decide) (by decide)).trans a10_980
  have a11_f80 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K11.acc (by decide) (by decide)).trans a10_f80
  have a11_fe4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K11.acc (by decide) (by decide)).trans a10_fe4
  have a11_1338 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K11.acc (by decide) (by decide)).trans a10_1338
  have a11_1358 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K11.acc (by decide) (by decide)).trans a10_1358
  clear a10_1358 a10_1338 a10_fe4 a10_f80 a10_980 a10_900 a10_200 a10_180 w10_44 b10_1004 b10_fa0 b10_920 b10_220 w10_50 w10_48 w10_40 w10_18 w10_10 g10_24 g10_11 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0xC24
  obtain ⟨n12, c12, u12⟩ := s11.block p2vZAc24 E11.self p2vZAc24_end
    ⟨trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem P2V n12 0xC26 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock p2vZAc24 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_8 : reg n12 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_10 : reg n12 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by
    rw [rb12, runBlock_reg _ _ _ a0 s11.zero (by decide), g11_10]
  have g12_11 : reg n12 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by
    rw [rb12, runBlock_reg _ _ _ a1 s11.zero (by decide), g11_11]
  have g12_24 : reg n12 (24 : Fin 32) = dhi := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_13 : reg n12 a3 = BitVec.ofNat 32 0x0 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vZAc24, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_11, g11_24, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4), (0x44, 0x4), (0x4C, 0x4)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_10 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m12]; exact w11_10
  have w12_18 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m12]; exact w11_18
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m12]; exact w11_40
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by rw [m12]; exact w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by rw [m12]; exact w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by rw [m12]; exact w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by rw [m12]; exact w11_50
  have b12_220 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m12]; exact b11_220
  have b12_920 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m12]; exact b11_920
  have b12_fa0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m12]; exact b11_fa0
  have b12_1004 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m12]; exact b11_1004
  have a12_180 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m12]; exact a11_180
  have a12_200 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m12]; exact a11_200
  have a12_900 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m12]; exact a11_900
  have a12_980 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m12]; exact a11_980
  have a12_f80 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m12]; exact a11_f80
  have a12_fe4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m12]; exact a11_fe4
  have a12_1338 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m12]; exact a11_1338
  have a12_1358 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m12]; exact a11_1358
  clear a11_1358 a11_1338 a11_fe4 a11_f80 a11_980 a11_900 a11_200 a11_180 w11_4c b11_1004 b11_fa0 b11_920 b11_220 w11_50 w11_48 w11_44 w11_40 w11_18 w11_10 g11_24 g11_11 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 rg11 W11 K11 fr11 s11 d11
  -- 0xC26: sw
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := p2v_sw F E12 s12 p2v_at_c26 (off' := 0xC28) (c := 0x54)
    (by decide) (by rw [g12_2]; p2v_addr) (by decide) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, P2vR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : P2vCode n13.mem := E12.fr F fr13
  have V13 : P2vSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg13 (8 : Fin 32), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [rg13 (9 : Fin 32), g12_9]
  have g13_10 : reg n13 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by rw [rg13 a0, g12_10]
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by rw [rg13 a1, g12_11]
  have g13_13 : reg n13 a3 = BitVec.ofNat 32 0x0 := by rw [rg13 a3, g12_13]
  have g13_24 : reg n13 (24 : Fin 32) = dhi := by rw [rg13 (24 : Fin 32), g12_24]
  have keep_kk13 : P2vKeepL B n0.mem n13.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4), (0x44, 0x4), (0x4C, 0x4), (0x54, 0x4)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_10 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K13.w32 (by decide) (by decide)).trans w12_10
  have w13_18 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K13.w32 (by decide) (by decide)).trans w12_18
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K13.w32 (by decide) (by decide)).trans w12_40
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := (K13.w32 (by decide) (by decide)).trans w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := (K13.w32 (by decide) (by decide)).trans w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := (K13.w32 (by decide) (by decide)).trans w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := (K13.w32 (by decide) (by decide)).trans w12_50
  have b13_220 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K13.b8 (by decide) (by decide)).trans b12_220
  have b13_920 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K13.b8 (by decide) (by decide)).trans b12_920
  have b13_fa0 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K13.b8 (by decide) (by decide)).trans b12_fa0
  have b13_1004 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K13.b8 (by decide) (by decide)).trans b12_1004
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x0 := by rw [W13, s12.zero]; rfl
  have a13_180 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K13.acc (by decide) (by decide)).trans a12_180
  have a13_200 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K13.acc (by decide) (by decide)).trans a12_200
  have a13_900 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K13.acc (by decide) (by decide)).trans a12_900
  have a13_980 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K13.acc (by decide) (by decide)).trans a12_980
  have a13_f80 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K13.acc (by decide) (by decide)).trans a12_f80
  have a13_fe4 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K13.acc (by decide) (by decide)).trans a12_fe4
  have a13_1338 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K13.acc (by decide) (by decide)).trans a12_1338
  have a13_1358 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K13.acc (by decide) (by decide)).trans a12_1358
  clear a12_1358 a12_1338 a12_fe4 a12_f80 a12_980 a12_900 a12_200 a12_180 b12_1004 b12_fa0 b12_920 b12_220 w12_50 w12_4c w12_48 w12_44 w12_40 w12_18 w12_10 g12_13 g12_24 g12_11 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0xC28
  obtain ⟨n14, c14, u14⟩ := s13.block p2vZAc28 E13.self p2vZAc28_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem P2V n14 0xC34 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock p2vZAc28 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_8 : reg n14 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by
    rw [rb14, runBlock_reg _ _ _ a0 s13.zero (by decide), g13_10]
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by
    rw [rb14, runBlock_reg _ _ _ a1 s13.zero (by decide), g13_11]
  have g14_13 : reg n14 a3 = BitVec.ofNat 32 0x0 := by
    rw [rb14, runBlock_reg _ _ _ a3 s13.zero (by decide), g13_13]
  have g14_24 : reg n14 (24 : Fin 32) = dhi := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_18 : reg n14 (18 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vZAc28, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_11, g13_13, g13_24, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_20 : reg n14 (20 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vZAc28, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_11, g13_13, g13_24, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_22 : reg n14 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vZAc28, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_11, g13_13, g13_24, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_23 : reg n14 (23 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vZAc28, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_11, g13_13, g13_24, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_25 : reg n14 (25 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vZAc28, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_11, g13_13, g13_24, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_26 : reg n14 (26 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vZAc28, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_11, g13_13, g13_24, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk14 : P2vKeepL B n0.mem n14.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4), (0x44, 0x4), (0x4C, 0x4), (0x54, 0x4)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_10 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m14]; exact w13_10
  have w14_18 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m14]; exact w13_18
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m14]; exact w13_40
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by rw [m14]; exact w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by rw [m14]; exact w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by rw [m14]; exact w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by rw [m14]; exact w13_50
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x0 := by rw [m14]; exact w13_54
  have b14_220 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m14]; exact b13_220
  have b14_920 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m14]; exact b13_920
  have b14_fa0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m14]; exact b13_fa0
  have b14_1004 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m14]; exact b13_1004
  have a14_180 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m14]; exact a13_180
  have a14_200 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m14]; exact a13_200
  have a14_900 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m14]; exact a13_900
  have a14_980 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m14]; exact a13_980
  have a14_f80 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m14]; exact a13_f80
  have a14_fe4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m14]; exact a13_fe4
  have a14_1338 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m14]; exact a13_1338
  have a14_1358 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m14]; exact a13_1358
  clear a13_1358 a13_1338 a13_fe4 a13_f80 a13_980 a13_900 a13_200 a13_180 w13_54 b13_1004 b13_fa0 b13_920 b13_220 w13_50 w13_4c w13_48 w13_44 w13_40 w13_18 w13_10 g13_24 g13_13 g13_11 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  -- 0xC34: sw
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := p2v_sw F E14 s14 p2v_at_c34 (off' := 0xC36) (c := 0x14)
    (by decide) (by rw [g14_2]; p2v_addr) (by decide) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, P2vR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : P2vCode n15.mem := E14.fr F fr15
  have V15 : P2vSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg15 (8 : Fin 32), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [rg15 (9 : Fin 32), g14_9]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by rw [rg15 a0, g14_10]
  have g15_11 : reg n15 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by rw [rg15 a1, g14_11]
  have g15_13 : reg n15 a3 = BitVec.ofNat 32 0x0 := by rw [rg15 a3, g14_13]
  have g15_18 : reg n15 (18 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg15 (18 : Fin 32), g14_18]
  have g15_20 : reg n15 (20 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg15 (20 : Fin 32), g14_20]
  have g15_22 : reg n15 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg15 (22 : Fin 32), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg15 (23 : Fin 32), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = dhi := by rw [rg15 (24 : Fin 32), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg15 (25 : Fin 32), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg15 (26 : Fin 32), g14_26]
  have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4), (0x44, 0x4), (0x4C, 0x4), (0x54, 0x4), (0x14, 0x4)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_10 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K15.w32 (by decide) (by decide)).trans w14_10
  have w15_18 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K15.w32 (by decide) (by decide)).trans w14_18
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K15.w32 (by decide) (by decide)).trans w14_40
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := (K15.w32 (by decide) (by decide)).trans w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := (K15.w32 (by decide) (by decide)).trans w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := (K15.w32 (by decide) (by decide)).trans w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := (K15.w32 (by decide) (by decide)).trans w14_50
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x0 := (K15.w32 (by decide) (by decide)).trans w14_54
  have b15_220 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K15.b8 (by decide) (by decide)).trans b14_220
  have b15_920 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K15.b8 (by decide) (by decide)).trans b14_920
  have b15_fa0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K15.b8 (by decide) (by decide)).trans b14_fa0
  have b15_1004 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K15.b8 (by decide) (by decide)).trans b14_1004
  have w15_14 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = (if (rem).toNat < 62 then rem else 62) := by rw [W15, g14_9]
  have a15_180 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K15.acc (by decide) (by decide)).trans a14_180
  have a15_200 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K15.acc (by decide) (by decide)).trans a14_200
  have a15_900 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K15.acc (by decide) (by decide)).trans a14_900
  have a15_980 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K15.acc (by decide) (by decide)).trans a14_980
  have a15_f80 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K15.acc (by decide) (by decide)).trans a14_f80
  have a15_fe4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K15.acc (by decide) (by decide)).trans a14_fe4
  have a15_1338 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K15.acc (by decide) (by decide)).trans a14_1338
  have a15_1358 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K15.acc (by decide) (by decide)).trans a14_1358
  clear a14_1358 a14_1338 a14_fe4 a14_f80 a14_980 a14_900 a14_200 a14_180 b14_1004 b14_fa0 b14_920 b14_220 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_18 w14_10 g14_26 g14_25 g14_23 g14_22 g14_20 g14_18 g14_24 g14_13 g14_11 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0xC36
  obtain ⟨n16, c16, u16⟩ := s15.block p2vZAc36 E15.self p2vZAc36_end
    ⟨trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem P2V n16 0xC38 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock p2vZAc36 (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
  have fr16 : ∀ x, P2vR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, P2vR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : P2vCode n16.mem := E15.fr F fr16
  have V16 : P2vSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by
    rw [rb16, runBlock_reg _ _ _ sp s15.zero (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (3 : Fin 32) s15.zero (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (4 : Fin 32) s15.zero (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb16, runBlock_reg _ _ _ (8 : Fin 32) s15.zero (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by
    rw [rb16, runBlock_reg _ _ _ (9 : Fin 32) s15.zero (by decide), g15_9]
  have g16_10 : reg n16 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by
    rw [rb16, runBlock_reg _ _ _ a0 s15.zero (by decide), g15_10]
  have g16_11 : reg n16 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by
    rw [rb16, runBlock_reg _ _ _ a1 s15.zero (by decide), g15_11]
  have g16_13 : reg n16 a3 = BitVec.ofNat 32 0x0 := by
    rw [rb16, runBlock_reg _ _ _ a3 s15.zero (by decide), g15_13]
  have g16_18 : reg n16 (18 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
  have g16_20 : reg n16 (20 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb16, runBlock_reg _ _ _ (20 : Fin 32) s15.zero (by decide), g15_20]
  have g16_22 : reg n16 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = dhi := by
    rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
  have g16_14 : reg n16 a4 = (if (rem).toNat < 62 then rem else 62) := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, p2vZAc36, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_9, g15_10, g15_11, g15_13, g15_18, g15_20, g15_22, g15_23, g15_24, g15_25, g15_26, s15.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4), (0x44, 0x4), (0x4C, 0x4), (0x54, 0x4), (0x14, 0x4)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_10 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m16]; exact w15_10
  have w16_14 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = (if (rem).toNat < 62 then rem else 62) := by rw [m16]; exact w15_14
  have w16_18 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m16]; exact w15_18
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m16]; exact w15_40
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by rw [m16]; exact w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by rw [m16]; exact w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by rw [m16]; exact w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by rw [m16]; exact w15_50
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x0 := by rw [m16]; exact w15_54
  have b16_220 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m16]; exact b15_220
  have b16_920 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m16]; exact b15_920
  have b16_fa0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m16]; exact b15_fa0
  have b16_1004 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m16]; exact b15_1004
  have a16_180 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m16]; exact a15_180
  have a16_200 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m16]; exact a15_200
  have a16_900 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m16]; exact a15_900
  have a16_980 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m16]; exact a15_980
  have a16_f80 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m16]; exact a15_f80
  have a16_fe4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m16]; exact a15_fe4
  have a16_1338 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m16]; exact a15_1338
  have a16_1358 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m16]; exact a15_1358
  clear a15_1358 a15_1338 a15_fe4 a15_f80 a15_980 a15_900 a15_200 a15_180 w15_14 b15_1004 b15_fa0 b15_920 b15_220 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_18 w15_10 g15_26 g15_25 g15_24 g15_23 g15_22 g15_20 g15_18 g15_13 g15_11 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  -- 0xC38: branch, not taken
  obtain ⟨n17, d17, u17⟩ := s16.notTaken E16.self 0xC3C p2v_at_c38
    (by decide) (by rw [g16_9, s16.zero]; exact br_beq_f (by split; exact hrem; decide))
  have s17 : St n17.mem P2V n17 0xC3C (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, P2vR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, P2vR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : P2vCode n17.mem := E16.fr F fr17
  have V17 : P2vSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u17.regs, g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = (if (rem).toNat < 62 then rem else 62) := by rw [u17.regs, g16_9]
  have g17_10 : reg n17 a0 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by rw [u17.regs, g16_10]
  have g17_11 : reg n17 a1 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by rw [u17.regs, g16_11]
  have g17_13 : reg n17 a3 = BitVec.ofNat 32 0x0 := by rw [u17.regs, g16_13]
  have g17_14 : reg n17 a4 = (if (rem).toNat < 62 then rem else 62) := by rw [u17.regs, g16_14]
  have g17_18 : reg n17 (18 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u17.regs, g16_18]
  have g17_20 : reg n17 (20 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u17.regs, g16_20]
  have g17_22 : reg n17 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u17.regs, g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u17.regs, g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = dhi := by rw [u17.regs, g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u17.regs, g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u17.regs, g16_26]
  have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0x18, 0x4), (0x50, 0x4), (0x48, 0x4), (0x44, 0x4), (0x4C, 0x4), (0x54, 0x4), (0x14, 0x4)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_10 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m17]; exact w16_10
  have w17_14 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = (if (rem).toNat < 62 then rem else 62) := by rw [m17]; exact w16_14
  have w17_18 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m17]; exact w16_18
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m17]; exact w16_40
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32) := by rw [m17]; exact w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32) := by rw [m17]; exact w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32) := by rw [m17]; exact w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32) := by rw [m17]; exact w16_50
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x0 := by rw [m17]; exact w16_54
  have b17_220 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m17]; exact b16_220
  have b17_920 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m17]; exact b16_920
  have b17_fa0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m17]; exact b16_fa0
  have b17_1004 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m17]; exact b16_1004
  have a17_180 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m17]; exact a16_180
  have a17_200 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m17]; exact a16_200
  have a17_900 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m17]; exact a16_900
  have a17_980 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m17]; exact a16_980
  have a17_f80 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m17]; exact a16_f80
  have a17_fe4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m17]; exact a16_fe4
  have a17_1338 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m17]; exact a16_1338
  have a17_1358 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m17]; exact a16_1358
  clear a16_1358 a16_1338 a16_fe4 a16_f80 a16_980 a16_900 a16_200 a16_180 b16_1004 b16_fa0 b16_920 b16_220 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_18 w16_14 w16_10 g16_14 g16_26 g16_25 g16_24 g16_23 g16_22 g16_20 g16_18 g16_13 g16_11 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
  exact .inr ⟨n17, t17, s17, E17, V17, fR17, g17_2, g17_3, g17_4, g17_8, g17_9, g17_13, g17_14, g17_18, g17_20, g17_22, g17_23, g17_24, g17_25, g17_26, w17_10, w17_14, w17_18, w17_40, w17_44, w17_48, w17_4c, w17_50, w17_54, b17_220, b17_920, b17_fa0, b17_1004, a17_180, a17_200, a17_900, a17_980, a17_f80, a17_fe4, a17_1338, a17_1358, keep_kk17.mono (by decide)⟩

end C3.RV32.P2v
