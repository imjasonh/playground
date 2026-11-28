import C3BootProofs.Proofs.P2vIvLib

/-!
# `p256VerifyPrehash`: the end of the inversion of `s`

From the inversion's exit at 0x610 to 0x690: `d`, normalized by `f`'s sign, is the inverse of `s` at offset 0x980, provided `f` is 1; otherwise `CtOption::unwrap` panics.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vIvE614 : List BInstr :=
  [.lui a3 0x3FCC4000, .aluImm .add a3 a3 0xD8, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x7E5, .aluImm .add (18 : Fin 32) sp 0x7FF, .aluImm .add (18 : Fin 32) (18 : Fin 32) 0x7E5]
theorem p2vIvE614_end : blockEnd p256VerifyPrehashCode 0x614 p2vIvE614 = some 0x634 := by
  simp only [p2vIvE614]
  rw [blockEnd, p2v_at_614]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_618]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_61c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_620]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_624]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_628]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_62c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_630]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvE63c : List BInstr :=
  [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x158, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x101]
theorem p2vIvE63c_end : blockEnd p256VerifyPrehashCode 0x63C p2vIvE63c = some 0x64C := by
  simp only [p2vIvE63c]
  rw [blockEnd, p2v_at_63c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_640]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_644]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_648]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvE654 : List BInstr :=
  [.aluImm .and a0 a0 0xFF, .alu .and a0 a0 (22 : Fin 32)]
theorem p2vIvE654_end : blockEnd p256VerifyPrehashCode 0x654 p2vIvE654 = some 0x65C := by
  simp only [p2vIvE654]
  rw [blockEnd, p2v_at_654]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_658]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvE664 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .aluImm .and (9 : Fin 32) a0 0xFF, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x20]
theorem p2vIvE664_end : blockEnd p256VerifyPrehashCode 0x664 p2vIvE664 = some 0x67E := by
  simp only [p2vIvE664]
  rw [blockEnd, p2v_at_664]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_666]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_66a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_66e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_672]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_676]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_67a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvE686 : List BInstr :=
  [.aluImm .add a0 x0 0x1]
theorem p2vIvE686_end : blockEnd p256VerifyPrehashCode 0x686 p2vIvE686 = some 0x688 := by
  simp only [p2vIvE686]
  rw [blockEnd, p2v_at_686]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_ive {B dlo dhi rem : Word} {fs gs ds es : BitVec 8} {qx qy qz rv sv zv fv gv dv ev : Nat} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0x610 (reg n0))
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
    (UC0 : P2vUpCode M0)
    (EC0 : P2vEcCode M0)
    (UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode)
    (N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code)
    (hfs : fs.toNat ≤ 1)
    (hds : ds.toNat ≤ 1) :
    (¬ ((fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8) ∧ True) ∧ Panics n0) ∨
    ((fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0x690 (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = (((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 ∧
        reg n' (9 : Fin 32) = ((((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF ∧
        reg n' (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 ∧
        reg n' (19 : Fin 32) = dlo ∧
        reg n' (21 : Fin 32) = dhi ∧
        reg n' (22 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg n' (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 ∧
        reg n' (24 : Fin 32) = rem ∧
        reg n' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
        reg n' (27 : Fin 32) = BitVec.ofNat 32 0x7 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = ((((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv ∧
        P2vKeepL B n0.mem n'.mem [(0xC80, 0x20), (0x980, 0x20), (0xC80, 0x1)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x610: lbu
  obtain ⟨n1, d1, u1⟩ := s0.lbu E0.self p2v_at_610 (off' := 0x614) (by decide)
  have s1 : St n1.mem P2V n1 0x614 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, P2vR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, P2vR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : P2vCode n1.mem := E0.fr F fr1
  have V1 : P2vSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_9]
  have g1_19 : reg n1 (19 : Fin 32) = dlo := by rw [u1.regs, upd_ne (by decide) (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = dhi := by rw [u1.regs, upd_ne (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = rem := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_26 : reg n1 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_12 : reg n1 a2 = (fs).zeroExtend 32 := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_26, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0x920 by p2v_addr, b0_920]
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  have b1_220 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m1]; exact b0_220
  have b1_920 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m1]; exact b0_920
  have b1_9a0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m1]; exact b0_9a0
  have b1_1004 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m1]; exact b0_1004
  have a1_120 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m1]; exact a0_120
  have a1_140 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m1]; exact a0_140
  have a1_160 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m1]; exact a0_160
  have a1_180 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m1]; exact a0_180
  have a1_1a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m1]; exact a0_1a0
  have a1_1c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m1]; exact a0_1c0
  have a1_200 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m1]; exact a0_200
  have a1_900 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m1]; exact a0_900
  have a1_980 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m1]; exact a0_980
  have a1_fe4 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m1]; exact a0_fe4
  -- 0x614
  obtain ⟨n2, c2, u2⟩ := s1.block p2vIvE614 E1.self p2vIvE614_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem P2V n2 0x634 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock p2vIvE614 (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
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
  have g2_8 : reg n2 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb2, runBlock_reg _ _ _ (8 : Fin 32) s1.zero (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [rb2, runBlock_reg _ _ _ (9 : Fin 32) s1.zero (by decide), g1_9]
  have g2_12 : reg n2 a2 = (fs).zeroExtend 32 := by
    rw [rb2, runBlock_reg _ _ _ a2 s1.zero (by decide), g1_12]
  have g2_19 : reg n2 (19 : Fin 32) = dlo := by
    rw [rb2, runBlock_reg _ _ _ (19 : Fin 32) s1.zero (by decide), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = dhi := by
    rw [rb2, runBlock_reg _ _ _ (21 : Fin 32) s1.zero (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb2, runBlock_reg _ _ _ (22 : Fin 32) s1.zero (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb2, runBlock_reg _ _ _ (23 : Fin 32) s1.zero (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = rem := by
    rw [rb2, runBlock_reg _ _ _ (24 : Fin 32) s1.zero (by decide), g1_24]
  have g2_26 : reg n2 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb2, runBlock_reg _ _ _ (26 : Fin 32) s1.zero (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb2, runBlock_reg _ _ _ (27 : Fin 32) s1.zero (by decide), g1_27]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vIvE614, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_8, g1_9, g1_12, g1_19, g1_21, g1_22, g1_23, g1_24, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g2_11 : reg n2 a1 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vIvE614, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_8, g1_9, g1_12, g1_19, g1_21, g1_22, g1_23, g1_24, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g2_13 : reg n2 a3 = BitVec.ofNat 32 (img% b2sOrder256Address) := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vIvE614, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_8, g1_9, g1_12, g1_19, g1_21, g1_22, g1_23, g1_24, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g2_18 : reg n2 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vIvE614, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_8, g1_9, g1_12, g1_19, g1_21, g1_22, g1_23, g1_24, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have b2_220 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m2]; exact b1_220
  have b2_920 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m2]; exact b1_920
  have b2_9a0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m2]; exact b1_9a0
  have b2_1004 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m2]; exact b1_1004
  have a2_120 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m2]; exact a1_120
  have a2_140 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m2]; exact a1_140
  have a2_160 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m2]; exact a1_160
  have a2_180 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m2]; exact a1_180
  have a2_1a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m2]; exact a1_1a0
  have a2_1c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m2]; exact a1_1c0
  have a2_200 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m2]; exact a1_200
  have a2_900 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m2]; exact a1_900
  have a2_980 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m2]; exact a1_980
  have a2_fe4 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m2]; exact a1_fe4
  clear a1_fe4 a1_980 a1_900 a1_200 a1_1c0 a1_1a0 a1_180 a1_160 a1_140 a1_120 b1_1004 b1_9a0 b1_920 b1_220 g1_12 g1_27 g1_26 g1_24 g1_23 g1_22 g1_21 g1_19 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x634: p2v_nrm8F
  obtain ⟨n3, c3, s3, sp3, rk3, A3, K3, fr3⟩ := p2v_nrm8F (co := 0xC80) (cx := 0xFE4)
    F E2 (UC0.p2v F fR2) (EC0.p2v F fR2) (codeIn_p2v F fR2 N80 (by decide) (by decide)) s2 p2v_at_634 p2v_at_638 (by decide) (by decide) g2_2
    g2_10 g2_11 g2_12 (zext_01 hfs) g2_13 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [show 0xFE4 + 0x20 = 0x1004 from rfl, b2_1004]; exact hds)
  rw [show 0xFE4 + 0x20 = 0x1004 from rfl, b2_1004, a2_fe4,
    accV_dataR F fR2 (by decide) (by decide)] at A3
  have t3 : Steps n0 n3 := t2.trans c3
  have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : P2vCode n3.mem := E2.fr F fr3
  have V3 : P2vSaves B n3.mem v := V2.keepL K3 (by decide)
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk3 (3 : Fin 32) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk3 (4 : Fin 32) (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [rk3 (8 : Fin 32) (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [rk3 (9 : Fin 32) (by decide), g2_9]
  have g3_18 : reg n3 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [rk3 (18 : Fin 32) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = dlo := by rw [rk3 (19 : Fin 32) (by decide), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = dhi := by rw [rk3 (21 : Fin 32) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk3 (22 : Fin 32) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rk3 (23 : Fin 32) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = rem := by rw [rk3 (24 : Fin 32) (by decide), g2_24]
  have g3_26 : reg n3 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk3 (26 : Fin 32) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk3 (27 : Fin 32) (by decide), g2_27]
  have g3_2 : reg n3 sp = B + 0x21A0 := sp3
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0xC80, 0x20)] := keep_kk2.trans K3
  clear keep_kk2
  have b3_220 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K3.b8 (by decide) (by decide)).trans b2_220
  have b3_920 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K3.b8 (by decide) (by decide)).trans b2_920
  have b3_9a0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K3.b8 (by decide) (by decide)).trans b2_9a0
  have b3_1004 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K3.b8 (by decide) (by decide)).trans b2_1004
  have a3_120 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K3.acc (by decide) (by decide)).trans a2_120
  have a3_140 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K3.acc (by decide) (by decide)).trans a2_140
  have a3_160 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K3.acc (by decide) (by decide)).trans a2_160
  have a3_180 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K3.acc (by decide) (by decide)).trans a2_180
  have a3_1a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K3.acc (by decide) (by decide)).trans a2_1a0
  have a3_1c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K3.acc (by decide) (by decide)).trans a2_1c0
  have a3_200 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K3.acc (by decide) (by decide)).trans a2_200
  have a3_900 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K3.acc (by decide) (by decide)).trans a2_900
  have a3_980 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K3.acc (by decide) (by decide)).trans a2_980
  have a3_fe4 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K3.acc (by decide) (by decide)).trans a2_fe4
  have a3_c80 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := A3
  clear a2_fe4 a2_980 a2_900 a2_200 a2_1c0 a2_1a0 a2_180 a2_160 a2_140 a2_120 b2_1004 b2_9a0 b2_920 b2_220 g2_18 g2_13 g2_11 g2_10 g2_27 g2_26 g2_24 g2_23 g2_22 g2_21 g2_19 g2_12 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0x63C
  obtain ⟨n4, c4, u4⟩ := s3.block p2vIvE63c E3.self p2vIvE63c_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem P2V n4 0x64C (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock p2vIvE63c (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb4, runBlock_reg _ _ _ (8 : Fin 32) s3.zero (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb4, runBlock_reg _ _ _ (18 : Fin 32) s3.zero (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = dlo := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = dhi := by
    rw [rb4, runBlock_reg _ _ _ (21 : Fin 32) s3.zero (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb4, runBlock_reg _ _ _ (22 : Fin 32) s3.zero (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb4, runBlock_reg _ _ _ (23 : Fin 32) s3.zero (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = rem := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_26 : reg n4 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vIvE63c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_18, g3_19, g3_21, g3_22, g3_23, g3_24, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g4_11 : reg n4 a1 = BitVec.ofNat 32 (img% p256OneAddress) := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vIvE63c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_18, g3_19, g3_21, g3_22, g3_23, g3_24, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0xC80, 0x20)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have b4_220 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m4]; exact b3_220
  have b4_920 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m4]; exact b3_920
  have b4_9a0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m4]; exact b3_9a0
  have b4_1004 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m4]; exact b3_1004
  have a4_120 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m4]; exact a3_120
  have a4_140 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m4]; exact a3_140
  have a4_160 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m4]; exact a3_160
  have a4_180 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m4]; exact a3_180
  have a4_1a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m4]; exact a3_1a0
  have a4_1c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m4]; exact a3_1c0
  have a4_200 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m4]; exact a3_200
  have a4_900 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m4]; exact a3_900
  have a4_980 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m4]; exact a3_980
  have a4_c80 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := by rw [m4]; exact a3_c80
  have a4_fe4 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m4]; exact a3_fe4
  clear a3_c80 a3_fe4 a3_980 a3_900 a3_200 a3_1c0 a3_1a0 a3_180 a3_160 a3_140 a3_120 b3_1004 b3_9a0 b3_920 b3_220 g3_2 g3_27 g3_26 g3_24 g3_23 g3_22 g3_21 g3_19 g3_18 g3_9 g3_8 g3_4 g3_3 V3 E3 fR3 t3 fr3 K3 A3 rk3 sp3 s3 c3
  -- 0x64C: p2v_ueq8F
  obtain ⟨n5, c5, s5, sp5, rk5, a0_5, K5, fr5⟩ := p2v_ueq8F (cp := 0x900)
    F E4 (codeIn_p2v F fR4 UE0 (by decide) (by decide)) s4 p2v_at_64c p2v_at_650 (by decide) (by decide) g4_2
    g4_10 g4_11 (by decide) (by decide) (by decide)
  rw [a4_900, accV_dataR F fR4 (by decide) (by decide)] at a0_5
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, P2vR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : P2vCode n5.mem := E4.fr F fr5
  have V5 : P2vSaves B n5.mem v := V4.keepL K5 (by decide)
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk5 (3 : Fin 32) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk5 (4 : Fin 32) (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [rk5 (8 : Fin 32) (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [rk5 (9 : Fin 32) (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [rk5 (18 : Fin 32) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = dlo := by rw [rk5 (19 : Fin 32) (by decide), g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = dhi := by rw [rk5 (21 : Fin 32) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk5 (22 : Fin 32) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rk5 (23 : Fin 32) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = rem := by rw [rk5 (24 : Fin 32) (by decide), g4_24]
  have g5_26 : reg n5 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk5 (26 : Fin 32) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk5 (27 : Fin 32) (by decide), g4_27]
  have g5_2 : reg n5 sp = B + 0x21A0 := sp5
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0xC80, 0x20)] := keep_kk4.trans K5
  clear keep_kk4
  have b5_220 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K5.b8 (by decide) (by decide)).trans b4_220
  have b5_920 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K5.b8 (by decide) (by decide)).trans b4_920
  have b5_9a0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K5.b8 (by decide) (by decide)).trans b4_9a0
  have b5_1004 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K5.b8 (by decide) (by decide)).trans b4_1004
  have a5_120 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K5.acc (by decide) (by decide)).trans a4_120
  have a5_140 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K5.acc (by decide) (by decide)).trans a4_140
  have a5_160 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K5.acc (by decide) (by decide)).trans a4_160
  have a5_180 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K5.acc (by decide) (by decide)).trans a4_180
  have a5_1a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K5.acc (by decide) (by decide)).trans a4_1a0
  have a5_1c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K5.acc (by decide) (by decide)).trans a4_1c0
  have a5_200 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K5.acc (by decide) (by decide)).trans a4_200
  have a5_900 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K5.acc (by decide) (by decide)).trans a4_900
  have a5_980 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K5.acc (by decide) (by decide)).trans a4_980
  have a5_c80 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := (K5.acc (by decide) (by decide)).trans a4_c80
  have a5_fe4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K5.acc (by decide) (by decide)).trans a4_fe4
  clear a4_fe4 a4_c80 a4_980 a4_900 a4_200 a4_1c0 a4_1a0 a4_180 a4_160 a4_140 a4_120 b4_1004 b4_9a0 b4_920 b4_220 g4_11 g4_10 g4_27 g4_26 g4_24 g4_23 g4_22 g4_21 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  by_cases hf1 : fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8
  rotate_left
  · have g5_10 : reg n5 a0 = BitVec.ofNat 32 0 := by rw [a0_5, ite_eq_right hf1]; rfl
    -- 0x654
    obtain ⟨n6, c6, u6⟩ := s5.block p2vIvE654 E5.self p2vIvE654_end
      ⟨trivial, trivial, trivial⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have s6 : St n6.mem P2V n6 0x65C (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have rb6 : ∀ q, reg n6 q = (runBlock p2vIvE654 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
    have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
      rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
    have g6_9 : reg n6 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
      rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
    have g6_18 : reg n6 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
      rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = dlo := by
      rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
    have g6_21 : reg n6 (21 : Fin 32) = dhi := by
      rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
    have g6_22 : reg n6 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb6, runBlock_reg _ _ _ (22 : Fin 32) s5.zero (by decide), g5_22]
    have g6_23 : reg n6 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
      rw [rb6, runBlock_reg _ _ _ (23 : Fin 32) s5.zero (by decide), g5_23]
    have g6_24 : reg n6 (24 : Fin 32) = rem := by
      rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
    have g6_26 : reg n6 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
      rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
      rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
    have g6_10 : reg n6 a0 = (BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1) := by
      rw [rb6]; simp +decide only [runBlock, BInstr.run, p2vIvE654, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_18, g5_19, g5_21, g5_22, g5_23, g5_24, g5_26, g5_27, s5.zero])
      all_goals first | with_reducible rfl | p2v_addr | decide
    have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0xC80, 0x20)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have b6_220 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m6]; exact b5_220
    have b6_920 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m6]; exact b5_920
    have b6_9a0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m6]; exact b5_9a0
    have b6_1004 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m6]; exact b5_1004
    have a6_120 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m6]; exact a5_120
    have a6_140 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m6]; exact a5_140
    have a6_160 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m6]; exact a5_160
    have a6_180 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m6]; exact a5_180
    have a6_1a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m6]; exact a5_1a0
    have a6_1c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m6]; exact a5_1c0
    have a6_200 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m6]; exact a5_200
    have a6_900 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m6]; exact a5_900
    have a6_980 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m6]; exact a5_980
    have a6_c80 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := by rw [m6]; exact a5_c80
    have a6_fe4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m6]; exact a5_fe4
    clear a5_fe4 a5_c80 a5_980 a5_900 a5_200 a5_1c0 a5_1a0 a5_180 a5_160 a5_140 a5_120 b5_1004 b5_9a0 b5_920 b5_220 g5_2 g5_27 g5_26 g5_24 g5_23 g5_22 g5_21 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 V5 E5 fR5 t5 fr5 K5 a0_5 rk5 sp5 s5 c5
    -- 0x65C: p2v_bbF
    obtain ⟨n7, c7, s7, sp7, rk7, a0_7, K7, fr7⟩ := p2v_bbF 
      F E6 s6 p2v_at_65c p2v_at_660 (by decide) (by decide) g6_2
    have t7 : Steps n0 n7 := t6.trans c7
    have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : P2vCode n7.mem := E6.fr F fr7
    have V7 : P2vSaves B n7.mem v := V6.keepL K7 (by decide)
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk7 (3 : Fin 32) (by decide), g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk7 (4 : Fin 32) (by decide), g6_4]
    have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [rk7 (8 : Fin 32) (by decide), g6_8]
    have g7_9 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [rk7 (9 : Fin 32) (by decide), g6_9]
    have g7_18 : reg n7 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [rk7 (18 : Fin 32) (by decide), g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = dlo := by rw [rk7 (19 : Fin 32) (by decide), g6_19]
    have g7_21 : reg n7 (21 : Fin 32) = dhi := by rw [rk7 (21 : Fin 32) (by decide), g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk7 (22 : Fin 32) (by decide), g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rk7 (23 : Fin 32) (by decide), g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = rem := by rw [rk7 (24 : Fin 32) (by decide), g6_24]
    have g7_26 : reg n7 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk7 (26 : Fin 32) (by decide), g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk7 (27 : Fin 32) (by decide), g6_27]
    have g7_2 : reg n7 sp = B + 0x21A0 := sp7
    have g7_10 : reg n7 a0 = (((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by rw [a0_7, g6_10]
    have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0xC80, 0x20)] := keep_kk6.trans K7
    clear keep_kk6
    have b7_220 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K7.b8 (by decide) (by decide)).trans b6_220
    have b7_920 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K7.b8 (by decide) (by decide)).trans b6_920
    have b7_9a0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K7.b8 (by decide) (by decide)).trans b6_9a0
    have b7_1004 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K7.b8 (by decide) (by decide)).trans b6_1004
    have a7_120 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K7.acc (by decide) (by decide)).trans a6_120
    have a7_140 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K7.acc (by decide) (by decide)).trans a6_140
    have a7_160 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K7.acc (by decide) (by decide)).trans a6_160
    have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K7.acc (by decide) (by decide)).trans a6_180
    have a7_1a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K7.acc (by decide) (by decide)).trans a6_1a0
    have a7_1c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K7.acc (by decide) (by decide)).trans a6_1c0
    have a7_200 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K7.acc (by decide) (by decide)).trans a6_200
    have a7_900 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K7.acc (by decide) (by decide)).trans a6_900
    have a7_980 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K7.acc (by decide) (by decide)).trans a6_980
    have a7_c80 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := (K7.acc (by decide) (by decide)).trans a6_c80
    have a7_fe4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K7.acc (by decide) (by decide)).trans a6_fe4
    clear a6_fe4 a6_c80 a6_980 a6_900 a6_200 a6_1c0 a6_1a0 a6_180 a6_160 a6_140 a6_120 b6_1004 b6_9a0 b6_920 b6_220 g6_10 g6_27 g6_26 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6 g5_10
    -- 0x664
    obtain ⟨n8, c8, u8⟩ := s7.block p2vIvE664 E7.self p2vIvE664_end
      ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have s8 : St n8.mem P2V n8 0x67E (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have rb8 : ∀ q, reg n8 q = (runBlock p2vIvE664 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
    have g8_18 : reg n8 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
      rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = dlo := by
      rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
    have g8_21 : reg n8 (21 : Fin 32) = dhi := by
      rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
      rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = rem := by
      rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
    have g8_26 : reg n8 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
      rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
      rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
    have g8_8 : reg n8 (8 : Fin 32) = (((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by
      rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vIvE664, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
      all_goals first | with_reducible rfl | p2v_addr | decide
    have g8_9 : reg n8 (9 : Fin 32) = ((((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
      rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vIvE664, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
      all_goals first | with_reducible rfl | p2v_addr | decide
    have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
      rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vIvE664, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
      all_goals first | with_reducible rfl | p2v_addr | decide
    have g8_11 : reg n8 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
      rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vIvE664, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
      all_goals first | with_reducible rfl | p2v_addr | decide
    have g8_12 : reg n8 a2 = BitVec.ofNat 32 0x20 := by
      rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vIvE664, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
      all_goals first | with_reducible rfl | p2v_addr | decide
    have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0xC80, 0x20)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have b8_220 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m8]; exact b7_220
    have b8_920 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m8]; exact b7_920
    have b8_9a0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m8]; exact b7_9a0
    have b8_1004 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m8]; exact b7_1004
    have a8_120 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m8]; exact a7_120
    have a8_140 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m8]; exact a7_140
    have a8_160 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m8]; exact a7_160
    have a8_180 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m8]; exact a7_180
    have a8_1a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m8]; exact a7_1a0
    have a8_1c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m8]; exact a7_1c0
    have a8_200 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m8]; exact a7_200
    have a8_900 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m8]; exact a7_900
    have a8_980 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m8]; exact a7_980
    have a8_c80 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := by rw [m8]; exact a7_c80
    have a8_fe4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m8]; exact a7_fe4
    clear a7_fe4 a7_c80 a7_980 a7_900 a7_200 a7_1c0 a7_1a0 a7_180 a7_160 a7_140 a7_120 b7_1004 b7_9a0 b7_920 b7_220 g7_10 g7_2 g7_27 g7_26 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 V7 E7 fR7 t7 fr7 K7 a0_7 rk7 sp7 s7 c7
    -- 0x67E: memcpy
    obtain ⟨n9, P9, K9, X9⟩ := p2v_mc (c := 0x980) (d := 0xC80) (N := 0x20) F E8 s8 p2v_at_67e p2v_at_682
      (by decide) (by decide) g8_2 g8_10 g8_11 g8_12
      (by decide) (by decide) (by decide)
    have s9 := P9.st
    have fr9 := P9.fr
    have t9 : Steps n0 n9 := t8.trans P9.steps
    have fR9 : ∀ x, P2vR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : P2vCode n9.mem := E8.fr F fr9
    have V9 : P2vSaves B n9.mem v := V8.keep K9 (by decide)
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [P9.regs sp (by decide), g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P9.regs (3 : Fin 32) (by decide), g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P9.regs (4 : Fin 32) (by decide), g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = (((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by rw [P9.regs (8 : Fin 32) (by decide), g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = ((((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [P9.regs (9 : Fin 32) (by decide), g8_9]
    have g9_18 : reg n9 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P9.regs (18 : Fin 32) (by decide), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = dlo := by rw [P9.regs (19 : Fin 32) (by decide), g8_19]
    have g9_21 : reg n9 (21 : Fin 32) = dhi := by rw [P9.regs (21 : Fin 32) (by decide), g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P9.regs (22 : Fin 32) (by decide), g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [P9.regs (23 : Fin 32) (by decide), g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = rem := by rw [P9.regs (24 : Fin 32) (by decide), g8_24]
    have g9_26 : reg n9 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P9.regs (26 : Fin 32) (by decide), g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P9.regs (27 : Fin 32) (by decide), g8_27]
    have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0xC80, 0x20), (0x980, 0x20)] := keep_kk8.trans K9.toL
    clear keep_kk8
    have b9_220 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K9.b8 (by decide) (by decide)).trans b8_220
    have b9_920 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K9.b8 (by decide) (by decide)).trans b8_920
    have b9_9a0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K9.b8 (by decide) (by decide)).trans b8_9a0
    have b9_1004 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K9.b8 (by decide) (by decide)).trans b8_1004
    have a9_120 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K9.acc (by decide) (by decide)).trans a8_120
    have a9_140 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K9.acc (by decide) (by decide)).trans a8_140
    have a9_160 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K9.acc (by decide) (by decide)).trans a8_160
    have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K9.acc (by decide) (by decide)).trans a8_180
    have a9_1a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K9.acc (by decide) (by decide)).trans a8_1a0
    have a9_1c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K9.acc (by decide) (by decide)).trans a8_1c0
    have a9_200 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K9.acc (by decide) (by decide)).trans a8_200
    have a9_900 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K9.acc (by decide) (by decide)).trans a8_900
    have a9_c80 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := (K9.acc (by decide) (by decide)).trans a8_c80
    have a9_fe4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K9.acc (by decide) (by decide)).trans a8_fe4
    have a9_980 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := (accV_S 8 fun q hq => by
      rw [show 0x980 + q = 0x980 + (0x0 + q) by omega, X9 (0x0 + q) (by omega),
        show 0xC80 + (0x0 + q) = 0xC80 + q by omega]).trans a8_c80
    clear a8_fe4 a8_c80 a8_980 a8_900 a8_200 a8_1c0 a8_1a0 a8_180 a8_160 a8_140 a8_120 b8_1004 b8_9a0 b8_920 b8_220 g8_12 g8_11 g8_10 g8_9 g8_8 g8_27 g8_26 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
    -- 0x686
    obtain ⟨n10, c10, u10⟩ := s9.block p2vIvE686 E9.self p2vIvE686_end
      ⟨trivial, trivial⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have s10 : St n10.mem P2V n10 0x688 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have rb10 : ∀ q, reg n10 q = (runBlock p2vIvE686 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
    have fr10 : ∀ x, P2vR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans c10
    have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : P2vCode n10.mem := E9.fr F fr10
    have V10 : P2vSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by
      rw [rb10, runBlock_reg _ _ _ sp s9.zero (by decide), g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb10, runBlock_reg _ _ _ (3 : Fin 32) s9.zero (by decide), g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb10, runBlock_reg _ _ _ (4 : Fin 32) s9.zero (by decide), g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = (((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by
      rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = ((((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
      rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
    have g10_18 : reg n10 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
      rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = dlo := by
      rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
    have g10_21 : reg n10 (21 : Fin 32) = dhi := by
      rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
      rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = rem := by
      rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
    have g10_26 : reg n10 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
      rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
      rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
    have g10_10 : reg n10 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vIvE686, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_21, g9_22, g9_23, g9_24, g9_26, g9_27, s9.zero])
      all_goals first | with_reducible rfl | p2v_addr | decide
    have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0xC80, 0x20), (0x980, 0x20)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
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
    have a10_980 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := by rw [m10]; exact a9_980
    have a10_c80 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := by rw [m10]; exact a9_c80
    have a10_fe4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m10]; exact a9_fe4
    clear a9_980 a9_fe4 a9_c80 a9_900 a9_200 a9_1c0 a9_1a0 a9_180 a9_160 a9_140 a9_120 b9_1004 b9_9a0 b9_920 b9_220 g9_27 g9_26 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 s9 X9 K9 P9
    -- 0x688: sb
    obtain ⟨n11, d11, s11, fr11, K11, W11, rg11⟩ := p2v_sb F E10 s10 p2v_at_688 (off' := 0x68C) (c := 0xC80)
      (by decide) (by rw [g10_26]; p2v_addr) (by decide)
    have t11 : Steps n0 n11 := t10.trans d11
    have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : P2vCode n11.mem := E10.fr F fr11
    have V11 : P2vSaves B n11.mem v := V10.keep K11 (by decide)
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rg11 sp, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg11 (3 : Fin 32), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg11 (4 : Fin 32), g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = (((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by rw [rg11 (8 : Fin 32), g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = ((((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [rg11 (9 : Fin 32), g10_9]
    have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x1 := by rw [rg11 a0, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [rg11 (18 : Fin 32), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = dlo := by rw [rg11 (19 : Fin 32), g10_19]
    have g11_21 : reg n11 (21 : Fin 32) = dhi := by rw [rg11 (21 : Fin 32), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg11 (22 : Fin 32), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg11 (23 : Fin 32), g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = rem := by rw [rg11 (24 : Fin 32), g10_24]
    have g11_26 : reg n11 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg11 (26 : Fin 32), g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg11 (27 : Fin 32), g10_27]
    have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0xC80, 0x20), (0x980, 0x20), (0xC80, 0x1)] := keep_kk10.trans K11.toL
    clear keep_kk10
    have b11_220 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K11.b8 (by decide) (by decide)).trans b10_220
    have b11_920 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K11.b8 (by decide) (by decide)).trans b10_920
    have b11_9a0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K11.b8 (by decide) (by decide)).trans b10_9a0
    have b11_1004 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K11.b8 (by decide) (by decide)).trans b10_1004
    have b11_c80 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = ((((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [W11, g10_8]
    have a11_120 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K11.acc (by decide) (by decide)).trans a10_120
    have a11_140 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K11.acc (by decide) (by decide)).trans a10_140
    have a11_160 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K11.acc (by decide) (by decide)).trans a10_160
    have a11_180 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K11.acc (by decide) (by decide)).trans a10_180
    have a11_1a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K11.acc (by decide) (by decide)).trans a10_1a0
    have a11_1c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K11.acc (by decide) (by decide)).trans a10_1c0
    have a11_200 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K11.acc (by decide) (by decide)).trans a10_200
    have a11_900 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K11.acc (by decide) (by decide)).trans a10_900
    have a11_980 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := (K11.acc (by decide) (by decide)).trans a10_980
    have a11_fe4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K11.acc (by decide) (by decide)).trans a10_fe4
    clear a10_fe4 a10_c80 a10_980 a10_900 a10_200 a10_1c0 a10_1a0 a10_180 a10_160 a10_140 a10_120 b10_1004 b10_9a0 b10_920 b10_220 g10_10 g10_27 g10_26 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
    -- 0x68C: branch, taken
    obtain ⟨n12, d12, u12⟩ := s11.taken E11.self 0x10C8 p2v_at_68c
      (by decide) (by rw [g11_9, g11_10]; decide)
    have s12 : St n12.mem P2V n12 0x10C8 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, P2vR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, P2vR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : P2vCode n12.mem := E11.fr F fr12
    have V12 : P2vSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
    have g12_8 : reg n12 (8 : Fin 32) = (((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by rw [u12.regs, g11_8]
    have g12_9 : reg n12 (9 : Fin 32) = ((((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [u12.regs, g11_9]
    have g12_10 : reg n12 a0 = BitVec.ofNat 32 0x1 := by rw [u12.regs, g11_10]
    have g12_18 : reg n12 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u12.regs, g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = dlo := by rw [u12.regs, g11_19]
    have g12_21 : reg n12 (21 : Fin 32) = dhi := by rw [u12.regs, g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u12.regs, g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [u12.regs, g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = rem := by rw [u12.regs, g11_24]
    have g12_26 : reg n12 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u12.regs, g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u12.regs, g11_27]
    have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0xC80, 0x20), (0x980, 0x20), (0xC80, 0x1)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have b12_220 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m12]; exact b11_220
    have b12_920 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m12]; exact b11_920
    have b12_9a0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m12]; exact b11_9a0
    have b12_c80 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = ((((BitVec.ofNat 32 0x0) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m12]; exact b11_c80
    have b12_1004 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m12]; exact b11_1004
    have a12_120 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m12]; exact a11_120
    have a12_140 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m12]; exact a11_140
    have a12_160 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m12]; exact a11_160
    have a12_180 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m12]; exact a11_180
    have a12_1a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m12]; exact a11_1a0
    have a12_1c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m12]; exact a11_1c0
    have a12_200 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m12]; exact a11_200
    have a12_900 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m12]; exact a11_900
    have a12_980 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := by rw [m12]; exact a11_980
    have a12_fe4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m12]; exact a11_fe4
    clear a11_fe4 a11_980 a11_900 a11_200 a11_1c0 a11_1a0 a11_180 a11_160 a11_140 a11_120 b11_c80 b11_1004 b11_9a0 b11_920 b11_220 g11_27 g11_26 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 rg11 W11 K11 fr11 s11 d11
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hf1 h0'), Panics.of_steps t12 (p2v_panic_10c8 F E12 s12 g12_2)⟩
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 1 := by rw [a0_5, ite_eq_left hf1]; rfl
  -- 0x654
  obtain ⟨n6, c6, u6⟩ := s5.block p2vIvE654 E5.self p2vIvE654_end
    ⟨trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem P2V n6 0x65C (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock p2vIvE654 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = dlo := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = dhi := by
    rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb6, runBlock_reg _ _ _ (22 : Fin 32) s5.zero (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb6, runBlock_reg _ _ _ (23 : Fin 32) s5.zero (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = rem := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_26 : reg n6 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_10 : reg n6 a0 = (BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1) := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, p2vIvE654, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_18, g5_19, g5_21, g5_22, g5_23, g5_24, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0xC80, 0x20)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have b6_220 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m6]; exact b5_220
  have b6_920 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m6]; exact b5_920
  have b6_9a0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m6]; exact b5_9a0
  have b6_1004 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m6]; exact b5_1004
  have a6_120 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m6]; exact a5_120
  have a6_140 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m6]; exact a5_140
  have a6_160 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m6]; exact a5_160
  have a6_180 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m6]; exact a5_180
  have a6_1a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m6]; exact a5_1a0
  have a6_1c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m6]; exact a5_1c0
  have a6_200 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m6]; exact a5_200
  have a6_900 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m6]; exact a5_900
  have a6_980 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m6]; exact a5_980
  have a6_c80 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := by rw [m6]; exact a5_c80
  have a6_fe4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m6]; exact a5_fe4
  clear a5_fe4 a5_c80 a5_980 a5_900 a5_200 a5_1c0 a5_1a0 a5_180 a5_160 a5_140 a5_120 b5_1004 b5_9a0 b5_920 b5_220 g5_2 g5_27 g5_26 g5_24 g5_23 g5_22 g5_21 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 V5 E5 fR5 t5 fr5 K5 a0_5 rk5 sp5 s5 c5
  -- 0x65C: p2v_bbF
  obtain ⟨n7, c7, s7, sp7, rk7, a0_7, K7, fr7⟩ := p2v_bbF 
    F E6 s6 p2v_at_65c p2v_at_660 (by decide) (by decide) g6_2
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : P2vCode n7.mem := E6.fr F fr7
  have V7 : P2vSaves B n7.mem v := V6.keepL K7 (by decide)
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk7 (3 : Fin 32) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk7 (4 : Fin 32) (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [rk7 (8 : Fin 32) (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [rk7 (9 : Fin 32) (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [rk7 (18 : Fin 32) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = dlo := by rw [rk7 (19 : Fin 32) (by decide), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = dhi := by rw [rk7 (21 : Fin 32) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk7 (22 : Fin 32) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rk7 (23 : Fin 32) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = rem := by rw [rk7 (24 : Fin 32) (by decide), g6_24]
  have g7_26 : reg n7 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk7 (26 : Fin 32) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk7 (27 : Fin 32) (by decide), g6_27]
  have g7_2 : reg n7 sp = B + 0x21A0 := sp7
  have g7_10 : reg n7 a0 = (((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by rw [a0_7, g6_10]
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0xC80, 0x20)] := keep_kk6.trans K7
  clear keep_kk6
  have b7_220 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K7.b8 (by decide) (by decide)).trans b6_220
  have b7_920 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K7.b8 (by decide) (by decide)).trans b6_920
  have b7_9a0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K7.b8 (by decide) (by decide)).trans b6_9a0
  have b7_1004 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K7.b8 (by decide) (by decide)).trans b6_1004
  have a7_120 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K7.acc (by decide) (by decide)).trans a6_120
  have a7_140 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K7.acc (by decide) (by decide)).trans a6_140
  have a7_160 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K7.acc (by decide) (by decide)).trans a6_160
  have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K7.acc (by decide) (by decide)).trans a6_180
  have a7_1a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K7.acc (by decide) (by decide)).trans a6_1a0
  have a7_1c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K7.acc (by decide) (by decide)).trans a6_1c0
  have a7_200 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K7.acc (by decide) (by decide)).trans a6_200
  have a7_900 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K7.acc (by decide) (by decide)).trans a6_900
  have a7_980 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K7.acc (by decide) (by decide)).trans a6_980
  have a7_c80 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := (K7.acc (by decide) (by decide)).trans a6_c80
  have a7_fe4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K7.acc (by decide) (by decide)).trans a6_fe4
  clear a6_fe4 a6_c80 a6_980 a6_900 a6_200 a6_1c0 a6_1a0 a6_180 a6_160 a6_140 a6_120 b6_1004 b6_9a0 b6_920 b6_220 g6_10 g6_27 g6_26 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6 g5_10
  -- 0x664
  obtain ⟨n8, c8, u8⟩ := s7.block p2vIvE664 E7.self p2vIvE664_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem P2V n8 0x67E (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock p2vIvE664 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_18 : reg n8 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = dlo := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = dhi := by
    rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = rem := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_26 : reg n8 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_8 : reg n8 (8 : Fin 32) = (((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vIvE664, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g8_9 : reg n8 (9 : Fin 32) = ((((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vIvE664, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vIvE664, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g8_11 : reg n8 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vIvE664, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g8_12 : reg n8 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vIvE664, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0xC80, 0x20)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have b8_220 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m8]; exact b7_220
  have b8_920 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m8]; exact b7_920
  have b8_9a0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m8]; exact b7_9a0
  have b8_1004 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m8]; exact b7_1004
  have a8_120 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m8]; exact a7_120
  have a8_140 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m8]; exact a7_140
  have a8_160 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m8]; exact a7_160
  have a8_180 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m8]; exact a7_180
  have a8_1a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m8]; exact a7_1a0
  have a8_1c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m8]; exact a7_1c0
  have a8_200 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m8]; exact a7_200
  have a8_900 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m8]; exact a7_900
  have a8_980 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m8]; exact a7_980
  have a8_c80 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := by rw [m8]; exact a7_c80
  have a8_fe4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m8]; exact a7_fe4
  clear a7_fe4 a7_c80 a7_980 a7_900 a7_200 a7_1c0 a7_1a0 a7_180 a7_160 a7_140 a7_120 b7_1004 b7_9a0 b7_920 b7_220 g7_10 g7_2 g7_27 g7_26 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 V7 E7 fR7 t7 fr7 K7 a0_7 rk7 sp7 s7 c7
  -- 0x67E: memcpy
  obtain ⟨n9, P9, K9, X9⟩ := p2v_mc (c := 0x980) (d := 0xC80) (N := 0x20) F E8 s8 p2v_at_67e p2v_at_682
    (by decide) (by decide) g8_2 g8_10 g8_11 g8_12
    (by decide) (by decide) (by decide)
  have s9 := P9.st
  have fr9 := P9.fr
  have t9 : Steps n0 n9 := t8.trans P9.steps
  have fR9 : ∀ x, P2vR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : P2vCode n9.mem := E8.fr F fr9
  have V9 : P2vSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [P9.regs sp (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P9.regs (3 : Fin 32) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P9.regs (4 : Fin 32) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = (((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by rw [P9.regs (8 : Fin 32) (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = ((((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [P9.regs (9 : Fin 32) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P9.regs (18 : Fin 32) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = dlo := by rw [P9.regs (19 : Fin 32) (by decide), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = dhi := by rw [P9.regs (21 : Fin 32) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P9.regs (22 : Fin 32) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [P9.regs (23 : Fin 32) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = rem := by rw [P9.regs (24 : Fin 32) (by decide), g8_24]
  have g9_26 : reg n9 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P9.regs (26 : Fin 32) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P9.regs (27 : Fin 32) (by decide), g8_27]
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0xC80, 0x20), (0x980, 0x20)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have b9_220 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K9.b8 (by decide) (by decide)).trans b8_220
  have b9_920 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K9.b8 (by decide) (by decide)).trans b8_920
  have b9_9a0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K9.b8 (by decide) (by decide)).trans b8_9a0
  have b9_1004 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K9.b8 (by decide) (by decide)).trans b8_1004
  have a9_120 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K9.acc (by decide) (by decide)).trans a8_120
  have a9_140 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K9.acc (by decide) (by decide)).trans a8_140
  have a9_160 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K9.acc (by decide) (by decide)).trans a8_160
  have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K9.acc (by decide) (by decide)).trans a8_180
  have a9_1a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K9.acc (by decide) (by decide)).trans a8_1a0
  have a9_1c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K9.acc (by decide) (by decide)).trans a8_1c0
  have a9_200 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K9.acc (by decide) (by decide)).trans a8_200
  have a9_900 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K9.acc (by decide) (by decide)).trans a8_900
  have a9_c80 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := (K9.acc (by decide) (by decide)).trans a8_c80
  have a9_fe4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K9.acc (by decide) (by decide)).trans a8_fe4
  have a9_980 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := (accV_S 8 fun q hq => by
    rw [show 0x980 + q = 0x980 + (0x0 + q) by omega, X9 (0x0 + q) (by omega),
      show 0xC80 + (0x0 + q) = 0xC80 + q by omega]).trans a8_c80
  clear a8_fe4 a8_c80 a8_980 a8_900 a8_200 a8_1c0 a8_1a0 a8_180 a8_160 a8_140 a8_120 b8_1004 b8_9a0 b8_920 b8_220 g8_12 g8_11 g8_10 g8_9 g8_8 g8_27 g8_26 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0x686
  obtain ⟨n10, c10, u10⟩ := s9.block p2vIvE686 E9.self p2vIvE686_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem P2V n10 0x688 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock p2vIvE686 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  have fr10 : ∀ x, P2vR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans c10
  have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : P2vCode n10.mem := E9.fr F fr10
  have V10 : P2vSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by
    rw [rb10, runBlock_reg _ _ _ sp s9.zero (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (3 : Fin 32) s9.zero (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (4 : Fin 32) s9.zero (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = (((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = ((((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = dlo := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = dhi := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = rem := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_26 : reg n10 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vIvE686, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_21, g9_22, g9_23, g9_24, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0xC80, 0x20), (0x980, 0x20)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
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
  have a10_980 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := by rw [m10]; exact a9_980
  have a10_c80 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := by rw [m10]; exact a9_c80
  have a10_fe4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m10]; exact a9_fe4
  clear a9_980 a9_fe4 a9_c80 a9_900 a9_200 a9_1c0 a9_1a0 a9_180 a9_160 a9_140 a9_120 b9_1004 b9_9a0 b9_920 b9_220 g9_27 g9_26 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 s9 X9 K9 P9
  -- 0x688: sb
  obtain ⟨n11, d11, s11, fr11, K11, W11, rg11⟩ := p2v_sb F E10 s10 p2v_at_688 (off' := 0x68C) (c := 0xC80)
    (by decide) (by rw [g10_26]; p2v_addr) (by decide)
  have t11 : Steps n0 n11 := t10.trans d11
  have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : P2vCode n11.mem := E10.fr F fr11
  have V11 : P2vSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rg11 sp, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg11 (3 : Fin 32), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg11 (4 : Fin 32), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = (((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by rw [rg11 (8 : Fin 32), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = ((((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [rg11 (9 : Fin 32), g10_9]
  have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x1 := by rw [rg11 a0, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [rg11 (18 : Fin 32), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = dlo := by rw [rg11 (19 : Fin 32), g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = dhi := by rw [rg11 (21 : Fin 32), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg11 (22 : Fin 32), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg11 (23 : Fin 32), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = rem := by rw [rg11 (24 : Fin 32), g10_24]
  have g11_26 : reg n11 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg11 (26 : Fin 32), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg11 (27 : Fin 32), g10_27]
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0xC80, 0x20), (0x980, 0x20), (0xC80, 0x1)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have b11_220 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K11.b8 (by decide) (by decide)).trans b10_220
  have b11_920 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K11.b8 (by decide) (by decide)).trans b10_920
  have b11_9a0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K11.b8 (by decide) (by decide)).trans b10_9a0
  have b11_1004 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K11.b8 (by decide) (by decide)).trans b10_1004
  have b11_c80 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = ((((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [W11, g10_8]
  have a11_120 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K11.acc (by decide) (by decide)).trans a10_120
  have a11_140 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K11.acc (by decide) (by decide)).trans a10_140
  have a11_160 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K11.acc (by decide) (by decide)).trans a10_160
  have a11_180 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K11.acc (by decide) (by decide)).trans a10_180
  have a11_1a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K11.acc (by decide) (by decide)).trans a10_1a0
  have a11_1c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K11.acc (by decide) (by decide)).trans a10_1c0
  have a11_200 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K11.acc (by decide) (by decide)).trans a10_200
  have a11_900 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K11.acc (by decide) (by decide)).trans a10_900
  have a11_980 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := (K11.acc (by decide) (by decide)).trans a10_980
  have a11_fe4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K11.acc (by decide) (by decide)).trans a10_fe4
  clear a10_fe4 a10_c80 a10_980 a10_900 a10_200 a10_1c0 a10_1a0 a10_180 a10_160 a10_140 a10_120 b10_1004 b10_9a0 b10_920 b10_220 g10_10 g10_27 g10_26 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x68C: branch, not taken
  obtain ⟨n12, d12, u12⟩ := s11.notTaken E11.self 0x690 p2v_at_68c
    (by decide) (by rw [g11_9, g11_10]; decide)
  have s12 : St n12.mem P2V n12 0x690 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, P2vR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, P2vR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : P2vCode n12.mem := E11.fr F fr12
  have V12 : P2vSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = (((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32 := by rw [u12.regs, g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = ((((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [u12.regs, g11_9]
  have g12_10 : reg n12 a0 = BitVec.ofNat 32 0x1 := by rw [u12.regs, g11_10]
  have g12_18 : reg n12 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u12.regs, g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = dlo := by rw [u12.regs, g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = dhi := by rw [u12.regs, g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u12.regs, g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [u12.regs, g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = rem := by rw [u12.regs, g11_24]
  have g12_26 : reg n12 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u12.regs, g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u12.regs, g11_27]
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0xC80, 0x20), (0x980, 0x20), (0xC80, 0x1)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have b12_220 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m12]; exact b11_220
  have b12_920 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m12]; exact b11_920
  have b12_9a0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m12]; exact b11_9a0
  have b12_c80 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = ((((BitVec.ofNat 32 0x1) &&& (BitVec.ofNat 32 0x1)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m12]; exact b11_c80
  have b12_1004 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m12]; exact b11_1004
  have a12_120 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m12]; exact a11_120
  have a12_140 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m12]; exact a11_140
  have a12_160 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m12]; exact a11_160
  have a12_180 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m12]; exact a11_180
  have a12_1a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m12]; exact a11_1a0
  have a12_1c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m12]; exact a11_1c0
  have a12_200 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m12]; exact a11_200
  have a12_900 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m12]; exact a11_900
  have a12_980 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) := by rw [m12]; exact a11_980
  have a12_fe4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m12]; exact a11_fe4
  clear a11_fe4 a11_980 a11_900 a11_200 a11_1c0 a11_1a0 a11_180 a11_160 a11_140 a11_120 b11_c80 b11_1004 b11_9a0 b11_920 b11_220 g11_27 g11_26 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 rg11 W11 K11 fr11 s11 d11
  exact .inr ⟨hf1, n12, t12, s12, E12, V12, fR12, g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_21, g12_22, g12_23, g12_24, g12_26, g12_27, b12_220, b12_920, b12_9a0, b12_c80, b12_1004, a12_120, a12_140, a12_160, a12_180, a12_1a0, a12_1c0, a12_200, a12_900, a12_980, a12_fe4, keep_kk12.mono (by decide)⟩

end C3.RV32.P2v
