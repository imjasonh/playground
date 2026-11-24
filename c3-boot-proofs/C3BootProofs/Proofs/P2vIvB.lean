import C3BootProofs.Proofs.P2vIvLib

/-!
# `p256VerifyPrehash`: the end of a batch of the inversion of `s`

From the divstep loop's exit at 0x51E to 0x60C: the batch's matrix is stored at 0xF80, `update_fg` applies it to `f` and `g` and `update_de` to `d` and `e`, and the steps left drop by the batch's size.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vIvB51e : List BInstr :=
  [.aluImm .add (26 : Fin 32) sp 0x7FF, .aluImm .add (26 : Fin 32) (26 : Fin 32) 0x121]
theorem p2vIvB51e_end : blockEnd p256VerifyPrehashCode 0x51E p2vIvB51e = some 0x526 := by
  simp only [p2vIvB51e]
  rw [blockEnd, p2v_at_51e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_522]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvB546 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x101, .aluImm .add a2 sp 0x200, .aluImm .add a3 sp 0x7FF, .aluImm .add a3 a3 0x781, .alu .add a4 x0 (18 : Fin 32)]
theorem p2vIvB546_end : blockEnd p256VerifyPrehashCode 0x546 p2vIvB546 = some 0x562 := by
  simp only [p2vIvB546]
  rw [blockEnd, p2v_at_546]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_54a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_54e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_552]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_556]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_558]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_55c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_560]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvB56a : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x101, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x24]
theorem p2vIvB56a_end : blockEnd p256VerifyPrehashCode 0x56A p2vIvB56a = some 0x57E := by
  simp only [p2vIvB56a]
  rw [blockEnd, p2v_at_56a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_56e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_572]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_576]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_57a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvB586 : List BInstr :=
  [.aluImm .add a0 sp 0x200, .aluImm .add a2 x0 0x24, .alu .add a1 x0 (23 : Fin 32)]
theorem p2vIvB586_end : blockEnd p256VerifyPrehashCode 0x586 p2vIvB586 = some 0x58E := by
  simp only [p2vIvB586]
  rw [blockEnd, p2v_at_586]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_588]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_58c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvB596 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x7E5, .aluImm .add a2 sp 0x7FF, .aluImm .add a2 a2 0x181, .aluImm .add a6 sp 0x7FF, .aluImm .add a6 a6 0x781, .lui a3 0x3FCC4000, .aluImm .add a3 a3 0xD8]
theorem p2vIvB596_end : blockEnd p256VerifyPrehashCode 0x596 p2vIvB596 = some 0x5BE := by
  simp only [p2vIvB596]
  rw [blockEnd, p2v_at_596]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_59a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_59e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5a2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5a6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5aa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5ae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5b2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5b6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5ba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvB5c0 : List BInstr :=
  [.alu .add a4 x0 (8 : Fin 32)]
theorem p2vIvB5c0_end : blockEnd p256VerifyPrehashCode 0x5C0 p2vIvB5c0 = some 0x5C2 := by
  simp only [p2vIvB5c0]
  rw [blockEnd, p2v_at_5c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvB5c4 : List BInstr :=
  [.alu .add a5 x0 (9 : Fin 32), .alu .add (17 : Fin 32) x0 (18 : Fin 32)]
theorem p2vIvB5c4_end : blockEnd p256VerifyPrehashCode 0x5C4 p2vIvB5c4 = some 0x5C8 := by
  simp only [p2vIvB5c4]
  rw [blockEnd, p2v_at_5c4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5c6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvB5d0 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x7E5, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x24]
theorem p2vIvB5d0_end : blockEnd p256VerifyPrehashCode 0x5D0 p2vIvB5d0 = some 0x5E4 := by
  simp only [p2vIvB5d0]
  rw [blockEnd, p2v_at_5d0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5d4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5d8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5dc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5e0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvB5ec : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a2 x0 0x24, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x4A5]
theorem p2vIvB5ec_end : blockEnd p256VerifyPrehashCode 0x5EC p2vIvB5ec = some 0x600 := by
  simp only [p2vIvB5ec]
  rw [blockEnd, p2v_at_5ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5f0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5f4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5f8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_5fc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vIvB608 : List BInstr :=
  [.alu .sub (24 : Fin 32) (24 : Fin 32) (18 : Fin 32)]
theorem p2vIvB608_end : blockEnd p256VerifyPrehashCode 0x608 p2vIvB608 = some 0x60C := by
  simp only [p2vIvB608]
  rw [blockEnd, p2v_at_608]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_ivb {B dlo dhi rem ulo uhi vlo vhi qlo qhi rlo rhi : Word} {ns : Nat} {fs gs ds es : BitVec 8} {qx qy qz rv sv zv fv gv dv ev : Nat} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0x51E (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_6 : reg n0 (6 : Fin 32) = rhi)
    (g0_7 : reg n0 (7 : Fin 32) = qhi)
    (g0_9 : reg n0 (9 : Fin 32) = ulo)
    (g0_12 : reg n0 a2 = vlo)
    (g0_16 : reg n0 a6 = vhi)
    (g0_17 : reg n0 a7 = uhi)
    (g0_18 : reg n0 (18 : Fin 32) = BitVec.ofNat 32 ns)
    (g0_19 : reg n0 (19 : Fin 32) = dlo)
    (g0_21 : reg n0 (21 : Fin 32) = dhi)
    (g0_22 : reg n0 (22 : Fin 32) = BitVec.ofNat 32 0x1)
    (g0_23 : reg n0 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4)
    (g0_24 : reg n0 (24 : Fin 32) = rem)
    (g0_25 : reg n0 (25 : Fin 32) = qlo)
    (g0_27 : reg n0 (27 : Fin 32) = BitVec.ofNat 32 0x7)
    (g0_30 : reg n0 (30 : Fin 32) = rlo)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1)
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
    (hns1 : 1 ≤ ns)
    (hns2 : ns ≤ 62)
    (UC0 : P2vUpCode M0)
    (hfs : fs.toNat ≤ 1)
    (hgs : gs.toNat ≤ 1)
    (hds : ds.toNat ≤ 1)
    (hes : es.toNat ≤ 1) :
    (¬ (∃ σ11a A11a, sgnVal σ11a A11a = sgnVal (fs).toNat (fv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧ (σ11a ≤ 1) ∧ ∃ σ11b A11b, sgnVal σ11b A11b = sgnVal (fs).toNat (fv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧ (σ11b ≤ 1) ∧ ∃ σ21a A21a, sgnVal σ21a A21a = sgnVal (ds).toNat (dv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧ (σ21a ≤ 1) ∧ ∃ σ21b A21b, sgnVal σ21b A21b = sgnVal (ds).toNat (dv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧ (σ21b ≤ 1) ∧ True) ∧ P2vRet B v n0 0) ∨
    (∃ σ11a A11a, sgnVal σ11a A11a = sgnVal (fs).toNat (fv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧
    (σ11a ≤ 1) ∧
    ∃ σ11b A11b, sgnVal σ11b A11b = sgnVal (fs).toNat (fv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧
    (σ11b ≤ 1) ∧
    ∃ σ21a A21a, sgnVal σ21a A21a = sgnVal (ds).toNat (dv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧
    (σ21a ≤ 1) ∧
    ∃ σ21b A21b, sgnVal σ21b A21b = sgnVal (ds).toNat (dv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧
    (σ21b ≤ 1) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0x60C (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 ∧
        reg n' (19 : Fin 32) = dlo ∧
        reg n' (21 : Fin 32) = dhi ∧
        reg n' (22 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg n' (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 ∧
        reg n' (24 : Fin 32) = (rem) - (BitVec.ofNat 32 ns) ∧
        reg n' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
        reg n' (27 : Fin 32) = BitVec.ofNat 32 0x7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = BitVec.ofNat 8 (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 ∧
        P2vKeepL B n0.mem n'.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24), (0xC80, 0x45), (0xFE4, 0x24), (0x980, 0x24)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x51E
  obtain ⟨n1, c1, u1⟩ := s0.block p2vIvB51e E0.self p2vIvB51e_end
    ⟨trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem P2V n1 0x526 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock p2vIvB51e (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_6 : reg n1 (6 : Fin 32) = rhi := by
    rw [rb1, runBlock_reg _ _ _ (6 : Fin 32) s0.zero (by decide), g0_6]
  have g1_7 : reg n1 (7 : Fin 32) = qhi := by
    rw [rb1, runBlock_reg _ _ _ (7 : Fin 32) s0.zero (by decide), g0_7]
  have g1_9 : reg n1 (9 : Fin 32) = ulo := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
  have g1_12 : reg n1 a2 = vlo := by
    rw [rb1, runBlock_reg _ _ _ a2 s0.zero (by decide), g0_12]
  have g1_16 : reg n1 a6 = vhi := by
    rw [rb1, runBlock_reg _ _ _ a6 s0.zero (by decide), g0_16]
  have g1_17 : reg n1 a7 = uhi := by
    rw [rb1, runBlock_reg _ _ _ a7 s0.zero (by decide), g0_17]
  have g1_18 : reg n1 (18 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = dlo := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = dhi := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = rem := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = qlo := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_27 : reg n1 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_30 : reg n1 (30 : Fin 32) = rlo := by
    rw [rb1, runBlock_reg _ _ _ (30 : Fin 32) s0.zero (by decide), g0_30]
  have g1_26 : reg n1 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vIvB51e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_6, g0_7, g0_9, g0_12, g0_16, g0_17, g0_18, g0_19, g0_21, g0_22, g0_23, g0_24, g0_25, g0_27, g0_30, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m1]; exact w0_50
  have w1_54 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m1]; exact w0_54
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
  -- 0x526: sw
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := p2v_sw F E1 s1 p2v_at_526 (off' := 0x52A) (c := 0xF80)
    (by decide) (by rw [g1_26]; p2v_addr) (by decide) (by decide)
  have t2 : Steps n0 n2 := t1.trans d2
  have fR2 : ∀ x, P2vR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : P2vCode n2.mem := E1.fr F fr2
  have V2 : P2vSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rg2 sp, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg2 (3 : Fin 32), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg2 (4 : Fin 32), g1_4]
  have g2_6 : reg n2 (6 : Fin 32) = rhi := by rw [rg2 (6 : Fin 32), g1_6]
  have g2_7 : reg n2 (7 : Fin 32) = qhi := by rw [rg2 (7 : Fin 32), g1_7]
  have g2_9 : reg n2 (9 : Fin 32) = ulo := by rw [rg2 (9 : Fin 32), g1_9]
  have g2_12 : reg n2 a2 = vlo := by rw [rg2 a2, g1_12]
  have g2_16 : reg n2 a6 = vhi := by rw [rg2 a6, g1_16]
  have g2_17 : reg n2 a7 = uhi := by rw [rg2 a7, g1_17]
  have g2_18 : reg n2 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [rg2 (18 : Fin 32), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = dlo := by rw [rg2 (19 : Fin 32), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = dhi := by rw [rg2 (21 : Fin 32), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg2 (22 : Fin 32), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg2 (23 : Fin 32), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = rem := by rw [rg2 (24 : Fin 32), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = qlo := by rw [rg2 (25 : Fin 32), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg2 (26 : Fin 32), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg2 (27 : Fin 32), g1_27]
  have g2_30 : reg n2 (30 : Fin 32) = rlo := by rw [rg2 (30 : Fin 32), g1_30]
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [(0xF80, 0x4)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K2.w32 (by decide) (by decide)).trans w1_50
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K2.w32 (by decide) (by decide)).trans w1_54
  have b2_220 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K2.b8 (by decide) (by decide)).trans b1_220
  have b2_920 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K2.b8 (by decide) (by decide)).trans b1_920
  have b2_9a0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K2.b8 (by decide) (by decide)).trans b1_9a0
  have b2_1004 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K2.b8 (by decide) (by decide)).trans b1_1004
  have w2_f80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [W2, g1_9]
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
  clear a1_fe4 a1_980 a1_900 a1_200 a1_1c0 a1_1a0 a1_180 a1_160 a1_140 a1_120 b1_1004 b1_9a0 b1_920 b1_220 w1_54 w1_50 g1_26 g1_30 g1_27 g1_25 g1_24 g1_23 g1_22 g1_21 g1_19 g1_18 g1_17 g1_16 g1_12 g1_9 g1_7 g1_6 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x52A: sw
  obtain ⟨n3, d3, s3, fr3, K3, W3, rg3⟩ := p2v_sw F E2 s2 p2v_at_52a (off' := 0x52E) (c := 0xF84)
    (by decide) (by rw [g2_26]; p2v_addr) (by decide) (by decide)
  have t3 : Steps n0 n3 := t2.trans d3
  have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : P2vCode n3.mem := E2.fr F fr3
  have V3 : P2vSaves B n3.mem v := V2.keep K3 (by decide)
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [rg3 sp, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg3 (3 : Fin 32), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg3 (4 : Fin 32), g2_4]
  have g3_6 : reg n3 (6 : Fin 32) = rhi := by rw [rg3 (6 : Fin 32), g2_6]
  have g3_7 : reg n3 (7 : Fin 32) = qhi := by rw [rg3 (7 : Fin 32), g2_7]
  have g3_9 : reg n3 (9 : Fin 32) = ulo := by rw [rg3 (9 : Fin 32), g2_9]
  have g3_12 : reg n3 a2 = vlo := by rw [rg3 a2, g2_12]
  have g3_16 : reg n3 a6 = vhi := by rw [rg3 a6, g2_16]
  have g3_17 : reg n3 a7 = uhi := by rw [rg3 a7, g2_17]
  have g3_18 : reg n3 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [rg3 (18 : Fin 32), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = dlo := by rw [rg3 (19 : Fin 32), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = dhi := by rw [rg3 (21 : Fin 32), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg3 (22 : Fin 32), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg3 (23 : Fin 32), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = rem := by rw [rg3 (24 : Fin 32), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = qlo := by rw [rg3 (25 : Fin 32), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg3 (26 : Fin 32), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg3 (27 : Fin 32), g2_27]
  have g3_30 : reg n3 (30 : Fin 32) = rlo := by rw [rg3 (30 : Fin 32), g2_30]
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0xF80, 0x4), (0xF84, 0x4)] := keep_kk2.trans K3.toL
  clear keep_kk2
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K3.w32 (by decide) (by decide)).trans w2_50
  have w3_54 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K3.w32 (by decide) (by decide)).trans w2_54
  have w3_f80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K3.w32 (by decide) (by decide)).trans w2_f80
  have b3_220 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K3.b8 (by decide) (by decide)).trans b2_220
  have b3_920 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K3.b8 (by decide) (by decide)).trans b2_920
  have b3_9a0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K3.b8 (by decide) (by decide)).trans b2_9a0
  have b3_1004 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K3.b8 (by decide) (by decide)).trans b2_1004
  have w3_f84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [W3, g2_17]
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
  clear a2_fe4 a2_980 a2_900 a2_200 a2_1c0 a2_1a0 a2_180 a2_160 a2_140 a2_120 w2_f80 b2_1004 b2_9a0 b2_920 b2_220 w2_54 w2_50 g2_30 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_19 g2_18 g2_17 g2_16 g2_12 g2_9 g2_7 g2_6 g2_4 g2_3 g2_2 V2 E2 fR2 t2 rg2 W2 K2 fr2 s2 d2
  -- 0x52E: sw
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := p2v_sw F E3 s3 p2v_at_52e (off' := 0x532) (c := 0xF88)
    (by decide) (by rw [g3_26]; p2v_addr) (by decide) (by decide)
  have t4 : Steps n0 n4 := t3.trans d4
  have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : P2vCode n4.mem := E3.fr F fr4
  have V4 : P2vSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rg4 sp, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg4 (3 : Fin 32), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg4 (4 : Fin 32), g3_4]
  have g4_6 : reg n4 (6 : Fin 32) = rhi := by rw [rg4 (6 : Fin 32), g3_6]
  have g4_7 : reg n4 (7 : Fin 32) = qhi := by rw [rg4 (7 : Fin 32), g3_7]
  have g4_9 : reg n4 (9 : Fin 32) = ulo := by rw [rg4 (9 : Fin 32), g3_9]
  have g4_12 : reg n4 a2 = vlo := by rw [rg4 a2, g3_12]
  have g4_16 : reg n4 a6 = vhi := by rw [rg4 a6, g3_16]
  have g4_17 : reg n4 a7 = uhi := by rw [rg4 a7, g3_17]
  have g4_18 : reg n4 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [rg4 (18 : Fin 32), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = dlo := by rw [rg4 (19 : Fin 32), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = dhi := by rw [rg4 (21 : Fin 32), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg4 (22 : Fin 32), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg4 (23 : Fin 32), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = rem := by rw [rg4 (24 : Fin 32), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = qlo := by rw [rg4 (25 : Fin 32), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg4 (26 : Fin 32), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg4 (27 : Fin 32), g3_27]
  have g4_30 : reg n4 (30 : Fin 32) = rlo := by rw [rg4 (30 : Fin 32), g3_30]
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4)] := keep_kk3.trans K4.toL
  clear keep_kk3
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K4.w32 (by decide) (by decide)).trans w3_50
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K4.w32 (by decide) (by decide)).trans w3_54
  have w4_f80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K4.w32 (by decide) (by decide)).trans w3_f80
  have w4_f84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K4.w32 (by decide) (by decide)).trans w3_f84
  have b4_220 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K4.b8 (by decide) (by decide)).trans b3_220
  have b4_920 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K4.b8 (by decide) (by decide)).trans b3_920
  have b4_9a0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K4.b8 (by decide) (by decide)).trans b3_9a0
  have b4_1004 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K4.b8 (by decide) (by decide)).trans b3_1004
  have w4_f88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [W4, g3_12]
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
  clear a3_fe4 a3_980 a3_900 a3_200 a3_1c0 a3_1a0 a3_180 a3_160 a3_140 a3_120 w3_f84 b3_1004 b3_9a0 b3_920 b3_220 w3_f80 w3_54 w3_50 g3_30 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_19 g3_18 g3_17 g3_16 g3_12 g3_9 g3_7 g3_6 g3_4 g3_3 g3_2 V3 E3 fR3 t3 rg3 W3 K3 fr3 s3 d3
  -- 0x532: sw
  obtain ⟨n5, d5, s5, fr5, K5, W5, rg5⟩ := p2v_sw F E4 s4 p2v_at_532 (off' := 0x536) (c := 0xF8C)
    (by decide) (by rw [g4_26]; p2v_addr) (by decide) (by decide)
  have t5 : Steps n0 n5 := t4.trans d5
  have fR5 : ∀ x, P2vR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : P2vCode n5.mem := E4.fr F fr5
  have V5 : P2vSaves B n5.mem v := V4.keep K5 (by decide)
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rg5 sp, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg5 (3 : Fin 32), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg5 (4 : Fin 32), g4_4]
  have g5_6 : reg n5 (6 : Fin 32) = rhi := by rw [rg5 (6 : Fin 32), g4_6]
  have g5_7 : reg n5 (7 : Fin 32) = qhi := by rw [rg5 (7 : Fin 32), g4_7]
  have g5_9 : reg n5 (9 : Fin 32) = ulo := by rw [rg5 (9 : Fin 32), g4_9]
  have g5_12 : reg n5 a2 = vlo := by rw [rg5 a2, g4_12]
  have g5_16 : reg n5 a6 = vhi := by rw [rg5 a6, g4_16]
  have g5_17 : reg n5 a7 = uhi := by rw [rg5 a7, g4_17]
  have g5_18 : reg n5 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [rg5 (18 : Fin 32), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = dlo := by rw [rg5 (19 : Fin 32), g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = dhi := by rw [rg5 (21 : Fin 32), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg5 (22 : Fin 32), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg5 (23 : Fin 32), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = rem := by rw [rg5 (24 : Fin 32), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = qlo := by rw [rg5 (25 : Fin 32), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg5 (26 : Fin 32), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg5 (27 : Fin 32), g4_27]
  have g5_30 : reg n5 (30 : Fin 32) = rlo := by rw [rg5 (30 : Fin 32), g4_30]
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4)] := keep_kk4.trans K5.toL
  clear keep_kk4
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K5.w32 (by decide) (by decide)).trans w4_50
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K5.w32 (by decide) (by decide)).trans w4_54
  have w5_f80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K5.w32 (by decide) (by decide)).trans w4_f80
  have w5_f84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K5.w32 (by decide) (by decide)).trans w4_f84
  have w5_f88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := (K5.w32 (by decide) (by decide)).trans w4_f88
  have b5_220 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K5.b8 (by decide) (by decide)).trans b4_220
  have b5_920 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K5.b8 (by decide) (by decide)).trans b4_920
  have b5_9a0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K5.b8 (by decide) (by decide)).trans b4_9a0
  have b5_1004 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K5.b8 (by decide) (by decide)).trans b4_1004
  have w5_f8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [W5, g4_16]
  have a5_120 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K5.acc (by decide) (by decide)).trans a4_120
  have a5_140 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K5.acc (by decide) (by decide)).trans a4_140
  have a5_160 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K5.acc (by decide) (by decide)).trans a4_160
  have a5_180 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K5.acc (by decide) (by decide)).trans a4_180
  have a5_1a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K5.acc (by decide) (by decide)).trans a4_1a0
  have a5_1c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K5.acc (by decide) (by decide)).trans a4_1c0
  have a5_200 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K5.acc (by decide) (by decide)).trans a4_200
  have a5_900 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K5.acc (by decide) (by decide)).trans a4_900
  have a5_980 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K5.acc (by decide) (by decide)).trans a4_980
  have a5_fe4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K5.acc (by decide) (by decide)).trans a4_fe4
  clear a4_fe4 a4_980 a4_900 a4_200 a4_1c0 a4_1a0 a4_180 a4_160 a4_140 a4_120 w4_f88 b4_1004 b4_9a0 b4_920 b4_220 w4_f84 w4_f80 w4_54 w4_50 g4_30 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_19 g4_18 g4_17 g4_16 g4_12 g4_9 g4_7 g4_6 g4_4 g4_3 g4_2 V4 E4 fR4 t4 rg4 W4 K4 fr4 s4 d4
  -- 0x536: sw
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := p2v_sw F E5 s5 p2v_at_536 (off' := 0x53A) (c := 0xF90)
    (by decide) (by rw [g5_26]; p2v_addr) (by decide) (by decide)
  have t6 : Steps n0 n6 := t5.trans d6
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rg6 sp, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg6 (3 : Fin 32), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg6 (4 : Fin 32), g5_4]
  have g6_6 : reg n6 (6 : Fin 32) = rhi := by rw [rg6 (6 : Fin 32), g5_6]
  have g6_7 : reg n6 (7 : Fin 32) = qhi := by rw [rg6 (7 : Fin 32), g5_7]
  have g6_9 : reg n6 (9 : Fin 32) = ulo := by rw [rg6 (9 : Fin 32), g5_9]
  have g6_12 : reg n6 a2 = vlo := by rw [rg6 a2, g5_12]
  have g6_16 : reg n6 a6 = vhi := by rw [rg6 a6, g5_16]
  have g6_17 : reg n6 a7 = uhi := by rw [rg6 a7, g5_17]
  have g6_18 : reg n6 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [rg6 (18 : Fin 32), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = dlo := by rw [rg6 (19 : Fin 32), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = dhi := by rw [rg6 (21 : Fin 32), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg6 (22 : Fin 32), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg6 (23 : Fin 32), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = rem := by rw [rg6 (24 : Fin 32), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = qlo := by rw [rg6 (25 : Fin 32), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg6 (26 : Fin 32), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg6 (27 : Fin 32), g5_27]
  have g6_30 : reg n6 (30 : Fin 32) = rlo := by rw [rg6 (30 : Fin 32), g5_30]
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K6.w32 (by decide) (by decide)).trans w5_50
  have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K6.w32 (by decide) (by decide)).trans w5_54
  have w6_f80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K6.w32 (by decide) (by decide)).trans w5_f80
  have w6_f84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K6.w32 (by decide) (by decide)).trans w5_f84
  have w6_f88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := (K6.w32 (by decide) (by decide)).trans w5_f88
  have w6_f8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := (K6.w32 (by decide) (by decide)).trans w5_f8c
  have b6_220 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K6.b8 (by decide) (by decide)).trans b5_220
  have b6_920 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K6.b8 (by decide) (by decide)).trans b5_920
  have b6_9a0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K6.b8 (by decide) (by decide)).trans b5_9a0
  have b6_1004 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K6.b8 (by decide) (by decide)).trans b5_1004
  have w6_f90 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [W6, g5_25]
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
  clear a5_fe4 a5_980 a5_900 a5_200 a5_1c0 a5_1a0 a5_180 a5_160 a5_140 a5_120 w5_f8c b5_1004 b5_9a0 b5_920 b5_220 w5_f88 w5_f84 w5_f80 w5_54 w5_50 g5_30 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_19 g5_18 g5_17 g5_16 g5_12 g5_9 g5_7 g5_6 g5_4 g5_3 g5_2 V5 E5 fR5 t5 rg5 W5 K5 fr5 s5 d5
  -- 0x53A: sw
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := p2v_sw F E6 s6 p2v_at_53a (off' := 0x53E) (c := 0xF94)
    (by decide) (by rw [g6_26]; p2v_addr) (by decide) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : P2vCode n7.mem := E6.fr F fr7
  have V7 : P2vSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_6 : reg n7 (6 : Fin 32) = rhi := by rw [rg7 (6 : Fin 32), g6_6]
  have g7_7 : reg n7 (7 : Fin 32) = qhi := by rw [rg7 (7 : Fin 32), g6_7]
  have g7_9 : reg n7 (9 : Fin 32) = ulo := by rw [rg7 (9 : Fin 32), g6_9]
  have g7_12 : reg n7 a2 = vlo := by rw [rg7 a2, g6_12]
  have g7_16 : reg n7 a6 = vhi := by rw [rg7 a6, g6_16]
  have g7_17 : reg n7 a7 = uhi := by rw [rg7 a7, g6_17]
  have g7_18 : reg n7 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [rg7 (18 : Fin 32), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = dlo := by rw [rg7 (19 : Fin 32), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = dhi := by rw [rg7 (21 : Fin 32), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg7 (22 : Fin 32), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg7 (23 : Fin 32), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = rem := by rw [rg7 (24 : Fin 32), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = qlo := by rw [rg7 (25 : Fin 32), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg7 (26 : Fin 32), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg7 (27 : Fin 32), g6_27]
  have g7_30 : reg n7 (30 : Fin 32) = rlo := by rw [rg7 (30 : Fin 32), g6_30]
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K7.w32 (by decide) (by decide)).trans w6_50
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K7.w32 (by decide) (by decide)).trans w6_54
  have w7_f80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K7.w32 (by decide) (by decide)).trans w6_f80
  have w7_f84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K7.w32 (by decide) (by decide)).trans w6_f84
  have w7_f88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := (K7.w32 (by decide) (by decide)).trans w6_f88
  have w7_f8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := (K7.w32 (by decide) (by decide)).trans w6_f8c
  have w7_f90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := (K7.w32 (by decide) (by decide)).trans w6_f90
  have b7_220 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K7.b8 (by decide) (by decide)).trans b6_220
  have b7_920 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K7.b8 (by decide) (by decide)).trans b6_920
  have b7_9a0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K7.b8 (by decide) (by decide)).trans b6_9a0
  have b7_1004 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K7.b8 (by decide) (by decide)).trans b6_1004
  have w7_f94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [W7, g6_7]
  have a7_120 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K7.acc (by decide) (by decide)).trans a6_120
  have a7_140 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K7.acc (by decide) (by decide)).trans a6_140
  have a7_160 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K7.acc (by decide) (by decide)).trans a6_160
  have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K7.acc (by decide) (by decide)).trans a6_180
  have a7_1a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K7.acc (by decide) (by decide)).trans a6_1a0
  have a7_1c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K7.acc (by decide) (by decide)).trans a6_1c0
  have a7_200 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K7.acc (by decide) (by decide)).trans a6_200
  have a7_900 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K7.acc (by decide) (by decide)).trans a6_900
  have a7_980 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K7.acc (by decide) (by decide)).trans a6_980
  have a7_fe4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K7.acc (by decide) (by decide)).trans a6_fe4
  clear a6_fe4 a6_980 a6_900 a6_200 a6_1c0 a6_1a0 a6_180 a6_160 a6_140 a6_120 w6_f90 b6_1004 b6_9a0 b6_920 b6_220 w6_f8c w6_f88 w6_f84 w6_f80 w6_54 w6_50 g6_30 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_17 g6_16 g6_12 g6_9 g6_7 g6_6 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
  -- 0x53E: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := p2v_sw F E7 s7 p2v_at_53e (off' := 0x542) (c := 0xF98)
    (by decide) (by rw [g7_26]; p2v_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, P2vR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : P2vCode n8.mem := E7.fr F fr8
  have V8 : P2vSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_6 : reg n8 (6 : Fin 32) = rhi := by rw [rg8 (6 : Fin 32), g7_6]
  have g8_7 : reg n8 (7 : Fin 32) = qhi := by rw [rg8 (7 : Fin 32), g7_7]
  have g8_9 : reg n8 (9 : Fin 32) = ulo := by rw [rg8 (9 : Fin 32), g7_9]
  have g8_12 : reg n8 a2 = vlo := by rw [rg8 a2, g7_12]
  have g8_16 : reg n8 a6 = vhi := by rw [rg8 a6, g7_16]
  have g8_17 : reg n8 a7 = uhi := by rw [rg8 a7, g7_17]
  have g8_18 : reg n8 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = dlo := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = dhi := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg8 (22 : Fin 32), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg8 (23 : Fin 32), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = rem := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = qlo := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg8 (26 : Fin 32), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg8 (27 : Fin 32), g7_27]
  have g8_30 : reg n8 (30 : Fin 32) = rlo := by rw [rg8 (30 : Fin 32), g7_30]
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K8.w32 (by decide) (by decide)).trans w7_50
  have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K8.w32 (by decide) (by decide)).trans w7_54
  have w8_f80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K8.w32 (by decide) (by decide)).trans w7_f80
  have w8_f84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K8.w32 (by decide) (by decide)).trans w7_f84
  have w8_f88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := (K8.w32 (by decide) (by decide)).trans w7_f88
  have w8_f8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := (K8.w32 (by decide) (by decide)).trans w7_f8c
  have w8_f90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := (K8.w32 (by decide) (by decide)).trans w7_f90
  have w8_f94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := (K8.w32 (by decide) (by decide)).trans w7_f94
  have b8_220 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K8.b8 (by decide) (by decide)).trans b7_220
  have b8_920 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K8.b8 (by decide) (by decide)).trans b7_920
  have b8_9a0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K8.b8 (by decide) (by decide)).trans b7_9a0
  have b8_1004 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K8.b8 (by decide) (by decide)).trans b7_1004
  have w8_f98 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [W8, g7_30]
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
  clear a7_fe4 a7_980 a7_900 a7_200 a7_1c0 a7_1a0 a7_180 a7_160 a7_140 a7_120 w7_f94 b7_1004 b7_9a0 b7_920 b7_220 w7_f90 w7_f8c w7_f88 w7_f84 w7_f80 w7_54 w7_50 g7_30 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_17 g7_16 g7_12 g7_9 g7_7 g7_6 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0x542: sw
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := p2v_sw F E8 s8 p2v_at_542 (off' := 0x546) (c := 0xF9C)
    (by decide) (by rw [g8_26]; p2v_addr) (by decide) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, P2vR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : P2vCode n9.mem := E8.fr F fr9
  have V9 : P2vSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_6 : reg n9 (6 : Fin 32) = rhi := by rw [rg9 (6 : Fin 32), g8_6]
  have g9_7 : reg n9 (7 : Fin 32) = qhi := by rw [rg9 (7 : Fin 32), g8_7]
  have g9_9 : reg n9 (9 : Fin 32) = ulo := by rw [rg9 (9 : Fin 32), g8_9]
  have g9_12 : reg n9 a2 = vlo := by rw [rg9 a2, g8_12]
  have g9_16 : reg n9 a6 = vhi := by rw [rg9 a6, g8_16]
  have g9_17 : reg n9 a7 = uhi := by rw [rg9 a7, g8_17]
  have g9_18 : reg n9 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [rg9 (18 : Fin 32), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = dlo := by rw [rg9 (19 : Fin 32), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = dhi := by rw [rg9 (21 : Fin 32), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg9 (22 : Fin 32), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rg9 (23 : Fin 32), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = rem := by rw [rg9 (24 : Fin 32), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = qlo := by rw [rg9 (25 : Fin 32), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg9 (26 : Fin 32), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rg9 (27 : Fin 32), g8_27]
  have g9_30 : reg n9 (30 : Fin 32) = rlo := by rw [rg9 (30 : Fin 32), g8_30]
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K9.w32 (by decide) (by decide)).trans w8_50
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K9.w32 (by decide) (by decide)).trans w8_54
  have w9_f80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K9.w32 (by decide) (by decide)).trans w8_f80
  have w9_f84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K9.w32 (by decide) (by decide)).trans w8_f84
  have w9_f88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := (K9.w32 (by decide) (by decide)).trans w8_f88
  have w9_f8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := (K9.w32 (by decide) (by decide)).trans w8_f8c
  have w9_f90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := (K9.w32 (by decide) (by decide)).trans w8_f90
  have w9_f94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := (K9.w32 (by decide) (by decide)).trans w8_f94
  have w9_f98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := (K9.w32 (by decide) (by decide)).trans w8_f98
  have b9_220 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K9.b8 (by decide) (by decide)).trans b8_220
  have b9_920 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K9.b8 (by decide) (by decide)).trans b8_920
  have b9_9a0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K9.b8 (by decide) (by decide)).trans b8_9a0
  have b9_1004 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K9.b8 (by decide) (by decide)).trans b8_1004
  have w9_f9c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [W9, g8_6]
  have a9_120 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K9.acc (by decide) (by decide)).trans a8_120
  have a9_140 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K9.acc (by decide) (by decide)).trans a8_140
  have a9_160 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K9.acc (by decide) (by decide)).trans a8_160
  have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K9.acc (by decide) (by decide)).trans a8_180
  have a9_1a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K9.acc (by decide) (by decide)).trans a8_1a0
  have a9_1c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K9.acc (by decide) (by decide)).trans a8_1c0
  have a9_200 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K9.acc (by decide) (by decide)).trans a8_200
  have a9_900 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K9.acc (by decide) (by decide)).trans a8_900
  have a9_980 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K9.acc (by decide) (by decide)).trans a8_980
  have a9_fe4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K9.acc (by decide) (by decide)).trans a8_fe4
  clear a8_fe4 a8_980 a8_900 a8_200 a8_1c0 a8_1a0 a8_180 a8_160 a8_140 a8_120 w8_f98 b8_1004 b8_9a0 b8_920 b8_220 w8_f94 w8_f90 w8_f8c w8_f88 w8_f84 w8_f80 w8_54 w8_50 g8_30 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_17 g8_16 g8_12 g8_9 g8_7 g8_6 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0x546
  obtain ⟨n10, c10, u10⟩ := s9.block p2vIvB546 E9.self p2vIvB546_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem P2V n10 0x562 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock p2vIvB546 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_6 : reg n10 (6 : Fin 32) = rhi := by
    rw [rb10, runBlock_reg _ _ _ (6 : Fin 32) s9.zero (by decide), g9_6]
  have g10_7 : reg n10 (7 : Fin 32) = qhi := by
    rw [rb10, runBlock_reg _ _ _ (7 : Fin 32) s9.zero (by decide), g9_7]
  have g10_9 : reg n10 (9 : Fin 32) = ulo := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_16 : reg n10 a6 = vhi := by
    rw [rb10, runBlock_reg _ _ _ a6 s9.zero (by decide), g9_16]
  have g10_17 : reg n10 a7 = uhi := by
    rw [rb10, runBlock_reg _ _ _ a7 s9.zero (by decide), g9_17]
  have g10_18 : reg n10 (18 : Fin 32) = BitVec.ofNat 32 ns := by
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
  have g10_25 : reg n10 (25 : Fin 32) = qlo := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_30 : reg n10 (30 : Fin 32) = rlo := by
    rw [rb10, runBlock_reg _ _ _ (30 : Fin 32) s9.zero (by decide), g9_30]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vIvB546, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_6, g9_7, g9_9, g9_12, g9_16, g9_17, g9_18, g9_19, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, g9_30, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g10_11 : reg n10 a1 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vIvB546, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_6, g9_7, g9_9, g9_12, g9_16, g9_17, g9_18, g9_19, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, g9_30, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g10_12 : reg n10 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vIvB546, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_6, g9_7, g9_9, g9_12, g9_16, g9_17, g9_18, g9_19, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, g9_30, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g10_13 : reg n10 a3 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vIvB546, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_6, g9_7, g9_9, g9_12, g9_16, g9_17, g9_18, g9_19, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, g9_30, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g10_14 : reg n10 a4 = BitVec.ofNat 32 ns := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vIvB546, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_6, g9_7, g9_9, g9_12, g9_16, g9_17, g9_18, g9_19, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, g9_30, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m10]; exact w9_50
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m10]; exact w9_54
  have w10_f80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [m10]; exact w9_f80
  have w10_f84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [m10]; exact w9_f84
  have w10_f88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [m10]; exact w9_f88
  have w10_f8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [m10]; exact w9_f8c
  have w10_f90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [m10]; exact w9_f90
  have w10_f94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [m10]; exact w9_f94
  have w10_f98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [m10]; exact w9_f98
  have w10_f9c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [m10]; exact w9_f9c
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
  clear a9_fe4 a9_980 a9_900 a9_200 a9_1c0 a9_1a0 a9_180 a9_160 a9_140 a9_120 w9_f9c b9_1004 b9_9a0 b9_920 b9_220 w9_f98 w9_f94 w9_f90 w9_f8c w9_f88 w9_f84 w9_f80 w9_54 w9_50 g9_30 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_17 g9_16 g9_12 g9_9 g9_7 g9_6 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  -- 0x562: p2v_ufg8F
  obtain ⟨n11, c11, s11, sp11, rk11, R1_11, R2_11, K11, fr11⟩ := p2v_ufg8F (co := 0xC80) (ca := 0x900) (cb := 0x200) (ct := 0xF80) (s := ns)
    F E10 (UC0.p2v F fR10) s10 p2v_at_562 p2v_at_566 (by decide) (by decide) g10_2
    g10_10 g10_11 g10_12 g10_13 g10_14 hns1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) 
    (by rw [show 0x900 + 0x20 = 0x920 from rfl, b10_920]; exact hfs)
    (by rw [show 0x200 + 0x20 = 0x220 from rfl, b10_220]; exact hgs)
  obtain ⟨σ11a, A11a, hσ0_11, e0_11, bb0_11, vv0_11⟩ := R1_11
  simp only [p2vI, p2vM, show 0x900 + 0x20 = 0x920 from rfl, show 0x200 + 0x20 = 0x220 from rfl,
    show 0xF80 + 0x0 = 0xF80 from rfl, show 0xF80 + 0x8 = 0xF88 from rfl] at e0_11
  rw [b10_920, a10_900, b10_220, a10_200,
    acc2_frame w10_f80 w10_f84, acc2_frame w10_f88 w10_f8c] at e0_11
  obtain ⟨σ11b, A11b, hσ1_11, e1_11, bb1_11, vv1_11⟩ := R2_11
  simp only [p2vI, p2vM, show 0x900 + 0x20 = 0x920 from rfl, show 0x200 + 0x20 = 0x220 from rfl,
    show 0xF80 + 0x10 = 0xF90 from rfl, show 0xF80 + 0x18 = 0xF98 from rfl] at e1_11
  rw [b10_920, a10_900, b10_220, a10_200,
    acc2_frame w10_f90 w10_f94, acc2_frame w10_f98 w10_f9c] at e1_11
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : P2vCode n11.mem := E10.fr F fr11
  have V11 : P2vSaves B n11.mem v := V10.keepL K11 (by decide)
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk11 (3 : Fin 32) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk11 (4 : Fin 32) (by decide), g10_4]
  have g11_9 : reg n11 (9 : Fin 32) = ulo := by rw [rk11 (9 : Fin 32) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [rk11 (18 : Fin 32) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = dlo := by rw [rk11 (19 : Fin 32) (by decide), g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = dhi := by rw [rk11 (21 : Fin 32) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk11 (22 : Fin 32) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rk11 (23 : Fin 32) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = rem := by rw [rk11 (24 : Fin 32) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = qlo := by rw [rk11 (25 : Fin 32) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk11 (26 : Fin 32) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk11 (27 : Fin 32) (by decide), g10_27]
  have g11_2 : reg n11 sp = B + 0x21A0 := sp11
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45)] := keep_kk10.trans K11
  clear keep_kk10
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K11.w32 (by decide) (by decide)).trans w10_50
  have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K11.w32 (by decide) (by decide)).trans w10_54
  have w11_f80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K11.w32 (by decide) (by decide)).trans w10_f80
  have w11_f84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K11.w32 (by decide) (by decide)).trans w10_f84
  have w11_f88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := (K11.w32 (by decide) (by decide)).trans w10_f88
  have w11_f8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := (K11.w32 (by decide) (by decide)).trans w10_f8c
  have w11_f90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := (K11.w32 (by decide) (by decide)).trans w10_f90
  have w11_f94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := (K11.w32 (by decide) (by decide)).trans w10_f94
  have w11_f98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := (K11.w32 (by decide) (by decide)).trans w10_f98
  have w11_f9c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := (K11.w32 (by decide) (by decide)).trans w10_f9c
  have b11_220 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K11.b8 (by decide) (by decide)).trans b10_220
  have b11_920 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K11.b8 (by decide) (by decide)).trans b10_920
  have b11_9a0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K11.b8 (by decide) (by decide)).trans b10_9a0
  have b11_1004 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K11.b8 (by decide) (by decide)).trans b10_1004
  have a11_120 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K11.acc (by decide) (by decide)).trans a10_120
  have a11_140 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K11.acc (by decide) (by decide)).trans a10_140
  have a11_160 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K11.acc (by decide) (by decide)).trans a10_160
  have a11_180 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K11.acc (by decide) (by decide)).trans a10_180
  have a11_1a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K11.acc (by decide) (by decide)).trans a10_1a0
  have a11_1c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K11.acc (by decide) (by decide)).trans a10_1c0
  have a11_200 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K11.acc (by decide) (by decide)).trans a10_200
  have a11_900 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K11.acc (by decide) (by decide)).trans a10_900
  have a11_980 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K11.acc (by decide) (by decide)).trans a10_980
  have a11_fe4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K11.acc (by decide) (by decide)).trans a10_fe4
  have a11_c80 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A11a / 2 ^ ns % 2 ^ 256 := vv0_11
  have a11_ca4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A11b / 2 ^ ns % 2 ^ 256 := vv1_11
  have b11_ca0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ11a := byte_of_toNat bb0_11
  have b11_cc4 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ11b := byte_of_toNat bb1_11
  clear a10_fe4 a10_980 a10_900 a10_200 a10_1c0 a10_1a0 a10_180 a10_160 a10_140 a10_120 b10_1004 b10_9a0 b10_920 b10_220 w10_f9c w10_f98 w10_f94 w10_f90 w10_f8c w10_f88 w10_f84 w10_f80 w10_54 w10_50 g10_14 g10_13 g10_12 g10_11 g10_10 g10_30 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_17 g10_16 g10_9 g10_7 g10_6 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x56A
  obtain ⟨n12, c12, u12⟩ := s11.block p2vIvB56a E11.self p2vIvB56a_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem P2V n12 0x57E (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock p2vIvB56a (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_9 : reg n12 (9 : Fin 32) = ulo := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = dlo := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = dhi := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = rem := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = qlo := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vIvB56a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_9, g11_18, g11_19, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vIvB56a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_9, g11_18, g11_19, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g12_12 : reg n12 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vIvB56a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_9, g11_18, g11_19, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m12]; exact w11_50
  have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m12]; exact w11_54
  have w12_f80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [m12]; exact w11_f80
  have w12_f84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [m12]; exact w11_f84
  have w12_f88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [m12]; exact w11_f88
  have w12_f8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [m12]; exact w11_f8c
  have w12_f90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [m12]; exact w11_f90
  have w12_f94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [m12]; exact w11_f94
  have w12_f98 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [m12]; exact w11_f98
  have w12_f9c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [m12]; exact w11_f9c
  have b12_220 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m12]; exact b11_220
  have b12_920 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m12]; exact b11_920
  have b12_9a0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m12]; exact b11_9a0
  have b12_ca0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ11a := by rw [m12]; exact b11_ca0
  have b12_cc4 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ11b := by rw [m12]; exact b11_cc4
  have b12_1004 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m12]; exact b11_1004
  have a12_120 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m12]; exact a11_120
  have a12_140 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m12]; exact a11_140
  have a12_160 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m12]; exact a11_160
  have a12_180 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m12]; exact a11_180
  have a12_1a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m12]; exact a11_1a0
  have a12_1c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m12]; exact a11_1c0
  have a12_200 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m12]; exact a11_200
  have a12_900 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m12]; exact a11_900
  have a12_980 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m12]; exact a11_980
  have a12_c80 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m12]; exact a11_c80
  have a12_ca4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m12]; exact a11_ca4
  have a12_fe4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m12]; exact a11_fe4
  clear b11_cc4 b11_ca0 a11_ca4 a11_c80 a11_fe4 a11_980 a11_900 a11_200 a11_1c0 a11_1a0 a11_180 a11_160 a11_140 a11_120 b11_1004 b11_9a0 b11_920 b11_220 w11_f9c w11_f98 w11_f94 w11_f90 w11_f8c w11_f88 w11_f84 w11_f80 w11_54 w11_50 g11_2 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_9 g11_4 g11_3 V11 E11 fR11 t11 vv1_11 bb1_11 vv0_11 bb0_11 fr11 K11 rk11 sp11 s11 c11
  -- 0x57E: memcpy
  obtain ⟨n13, P13, K13, X13⟩ := p2v_mc (c := 0x900) (d := 0xC80) (N := 0x24) F E12 s12 p2v_at_57e p2v_at_582
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
  have g13_9 : reg n13 (9 : Fin 32) = ulo := by rw [P13.regs (9 : Fin 32) (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [P13.regs (18 : Fin 32) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = dlo := by rw [P13.regs (19 : Fin 32) (by decide), g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = dhi := by rw [P13.regs (21 : Fin 32) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P13.regs (22 : Fin 32) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [P13.regs (23 : Fin 32) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = rem := by rw [P13.regs (24 : Fin 32) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = qlo := by rw [P13.regs (25 : Fin 32) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P13.regs (26 : Fin 32) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P13.regs (27 : Fin 32) (by decide), g12_27]
  have keep_kk13 : P2vKeepL B n0.mem n13.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K13.w32 (by decide) (by decide)).trans w12_50
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K13.w32 (by decide) (by decide)).trans w12_54
  have w13_f80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K13.w32 (by decide) (by decide)).trans w12_f80
  have w13_f84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K13.w32 (by decide) (by decide)).trans w12_f84
  have w13_f88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := (K13.w32 (by decide) (by decide)).trans w12_f88
  have w13_f8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := (K13.w32 (by decide) (by decide)).trans w12_f8c
  have w13_f90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := (K13.w32 (by decide) (by decide)).trans w12_f90
  have w13_f94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := (K13.w32 (by decide) (by decide)).trans w12_f94
  have w13_f98 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := (K13.w32 (by decide) (by decide)).trans w12_f98
  have w13_f9c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := (K13.w32 (by decide) (by decide)).trans w12_f9c
  have b13_220 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K13.b8 (by decide) (by decide)).trans b12_220
  have b13_9a0 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K13.b8 (by decide) (by decide)).trans b12_9a0
  have b13_ca0 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ11a := (K13.b8 (by decide) (by decide)).trans b12_ca0
  have b13_cc4 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ11b := (K13.b8 (by decide) (by decide)).trans b12_cc4
  have b13_1004 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K13.b8 (by decide) (by decide)).trans b12_1004
  have b13_920 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := by rw [show 0x920 = 0x900 + 0x20 from rfl, X13 0x20 (by decide)]; exact b12_ca0
  have a13_120 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K13.acc (by decide) (by decide)).trans a12_120
  have a13_140 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K13.acc (by decide) (by decide)).trans a12_140
  have a13_160 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K13.acc (by decide) (by decide)).trans a12_160
  have a13_180 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K13.acc (by decide) (by decide)).trans a12_180
  have a13_1a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K13.acc (by decide) (by decide)).trans a12_1a0
  have a13_1c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K13.acc (by decide) (by decide)).trans a12_1c0
  have a13_200 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K13.acc (by decide) (by decide)).trans a12_200
  have a13_980 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K13.acc (by decide) (by decide)).trans a12_980
  have a13_c80 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A11a / 2 ^ ns % 2 ^ 256 := (K13.acc (by decide) (by decide)).trans a12_c80
  have a13_ca4 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A11b / 2 ^ ns % 2 ^ 256 := (K13.acc (by decide) (by decide)).trans a12_ca4
  have a13_fe4 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K13.acc (by decide) (by decide)).trans a12_fe4
  have a13_900 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := (accV_S 8 fun q hq => by
    rw [show 0x900 + q = 0x900 + (0x0 + q) by omega, X13 (0x0 + q) (by omega),
      show 0xC80 + (0x0 + q) = 0xC80 + q by omega]).trans a12_c80
  clear a12_fe4 a12_ca4 a12_c80 a12_980 a12_900 a12_200 a12_1c0 a12_1a0 a12_180 a12_160 a12_140 a12_120 b12_1004 b12_cc4 b12_ca0 b12_9a0 b12_920 b12_220 w12_f9c w12_f98 w12_f94 w12_f90 w12_f8c w12_f88 w12_f84 w12_f80 w12_54 w12_50 g12_12 g12_11 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x586
  obtain ⟨n14, c14, u14⟩ := s13.block p2vIvB586 E13.self p2vIvB586_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem P2V n14 0x58E (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock p2vIvB586 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_9 : reg n14 (9 : Fin 32) = ulo := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = dlo := by
    rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
  have g14_21 : reg n14 (21 : Fin 32) = dhi := by
    rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb14, runBlock_reg _ _ _ (22 : Fin 32) s13.zero (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb14, runBlock_reg _ _ _ (23 : Fin 32) s13.zero (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = rem := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = qlo := by
    rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vIvB586, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_9, g13_18, g13_19, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_11 : reg n14 a1 = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vIvB586, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_9, g13_18, g13_19, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_12 : reg n14 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vIvB586, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_9, g13_18, g13_19, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk14 : P2vKeepL B n0.mem n14.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m14]; exact w13_50
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m14]; exact w13_54
  have w14_f80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [m14]; exact w13_f80
  have w14_f84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [m14]; exact w13_f84
  have w14_f88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [m14]; exact w13_f88
  have w14_f8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [m14]; exact w13_f8c
  have w14_f90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [m14]; exact w13_f90
  have w14_f94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [m14]; exact w13_f94
  have w14_f98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [m14]; exact w13_f98
  have w14_f9c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [m14]; exact w13_f9c
  have b14_220 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m14]; exact b13_220
  have b14_920 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := by rw [m14]; exact b13_920
  have b14_9a0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m14]; exact b13_9a0
  have b14_ca0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ11a := by rw [m14]; exact b13_ca0
  have b14_cc4 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ11b := by rw [m14]; exact b13_cc4
  have b14_1004 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m14]; exact b13_1004
  have a14_120 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m14]; exact a13_120
  have a14_140 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m14]; exact a13_140
  have a14_160 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m14]; exact a13_160
  have a14_180 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m14]; exact a13_180
  have a14_1a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m14]; exact a13_1a0
  have a14_1c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m14]; exact a13_1c0
  have a14_200 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m14]; exact a13_200
  have a14_900 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m14]; exact a13_900
  have a14_980 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m14]; exact a13_980
  have a14_c80 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m14]; exact a13_c80
  have a14_ca4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m14]; exact a13_ca4
  have a14_fe4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m14]; exact a13_fe4
  clear a13_900 a13_fe4 a13_ca4 a13_c80 a13_980 a13_200 a13_1c0 a13_1a0 a13_180 a13_160 a13_140 a13_120 b13_920 b13_1004 b13_cc4 b13_ca0 b13_9a0 b13_220 w13_f9c w13_f98 w13_f94 w13_f90 w13_f8c w13_f88 w13_f84 w13_f80 w13_54 w13_50 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_19 g13_18 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 s13 X13 K13 P13
  -- 0x58E: memcpy
  obtain ⟨n15, P15, K15, X15⟩ := p2v_mc (c := 0x200) (d := 0xCA4) (N := 0x24) F E14 s14 p2v_at_58e p2v_at_592
    (by decide) (by decide) g14_2 g14_10 g14_11 g14_12
    (by decide) (by decide) (by decide)
  have s15 := P15.st
  have fr15 := P15.fr
  have t15 : Steps n0 n15 := t14.trans P15.steps
  have fR15 : ∀ x, P2vR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : P2vCode n15.mem := E14.fr F fr15
  have V15 : P2vSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [P15.regs sp (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P15.regs (3 : Fin 32) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P15.regs (4 : Fin 32) (by decide), g14_4]
  have g15_9 : reg n15 (9 : Fin 32) = ulo := by rw [P15.regs (9 : Fin 32) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [P15.regs (18 : Fin 32) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = dlo := by rw [P15.regs (19 : Fin 32) (by decide), g14_19]
  have g15_21 : reg n15 (21 : Fin 32) = dhi := by rw [P15.regs (21 : Fin 32) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P15.regs (22 : Fin 32) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [P15.regs (23 : Fin 32) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = rem := by rw [P15.regs (24 : Fin 32) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = qlo := by rw [P15.regs (25 : Fin 32) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P15.regs (26 : Fin 32) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P15.regs (27 : Fin 32) (by decide), g14_27]
  have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K15.w32 (by decide) (by decide)).trans w14_50
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K15.w32 (by decide) (by decide)).trans w14_54
  have w15_f80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K15.w32 (by decide) (by decide)).trans w14_f80
  have w15_f84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K15.w32 (by decide) (by decide)).trans w14_f84
  have w15_f88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := (K15.w32 (by decide) (by decide)).trans w14_f88
  have w15_f8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := (K15.w32 (by decide) (by decide)).trans w14_f8c
  have w15_f90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := (K15.w32 (by decide) (by decide)).trans w14_f90
  have w15_f94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := (K15.w32 (by decide) (by decide)).trans w14_f94
  have w15_f98 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := (K15.w32 (by decide) (by decide)).trans w14_f98
  have w15_f9c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := (K15.w32 (by decide) (by decide)).trans w14_f9c
  have b15_920 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := (K15.b8 (by decide) (by decide)).trans b14_920
  have b15_9a0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K15.b8 (by decide) (by decide)).trans b14_9a0
  have b15_ca0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ11a := (K15.b8 (by decide) (by decide)).trans b14_ca0
  have b15_cc4 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ11b := (K15.b8 (by decide) (by decide)).trans b14_cc4
  have b15_1004 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K15.b8 (by decide) (by decide)).trans b14_1004
  have b15_220 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := by rw [show 0x220 = 0x200 + 0x20 from rfl, X15 0x20 (by decide)]; exact b14_cc4
  have a15_120 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K15.acc (by decide) (by decide)).trans a14_120
  have a15_140 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K15.acc (by decide) (by decide)).trans a14_140
  have a15_160 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K15.acc (by decide) (by decide)).trans a14_160
  have a15_180 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K15.acc (by decide) (by decide)).trans a14_180
  have a15_1a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K15.acc (by decide) (by decide)).trans a14_1a0
  have a15_1c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K15.acc (by decide) (by decide)).trans a14_1c0
  have a15_900 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := (K15.acc (by decide) (by decide)).trans a14_900
  have a15_980 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K15.acc (by decide) (by decide)).trans a14_980
  have a15_c80 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A11a / 2 ^ ns % 2 ^ 256 := (K15.acc (by decide) (by decide)).trans a14_c80
  have a15_ca4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A11b / 2 ^ ns % 2 ^ 256 := (K15.acc (by decide) (by decide)).trans a14_ca4
  have a15_fe4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K15.acc (by decide) (by decide)).trans a14_fe4
  have a15_200 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := (accV_S 8 fun q hq => by
    rw [show 0x200 + q = 0x200 + (0x0 + q) by omega, X15 (0x0 + q) (by omega),
      show 0xCA4 + (0x0 + q) = 0xCA4 + q by omega]).trans a14_ca4
  clear a14_fe4 a14_ca4 a14_c80 a14_980 a14_900 a14_200 a14_1c0 a14_1a0 a14_180 a14_160 a14_140 a14_120 b14_1004 b14_cc4 b14_ca0 b14_9a0 b14_920 b14_220 w14_f9c w14_f98 w14_f94 w14_f90 w14_f8c w14_f88 w14_f84 w14_f80 w14_54 w14_50 g14_12 g14_11 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_19 g14_18 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0x596
  obtain ⟨n16, c16, u16⟩ := s15.block p2vIvB596 E15.self p2vIvB596_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem P2V n16 0x5BE (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock p2vIvB596 (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
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
  have g16_9 : reg n16 (9 : Fin 32) = ulo := by
    rw [rb16, runBlock_reg _ _ _ (9 : Fin 32) s15.zero (by decide), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = dlo := by
    rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
  have g16_21 : reg n16 (21 : Fin 32) = dhi := by
    rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = rem := by
    rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = qlo := by
    rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
  have g16_10 : reg n16 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, p2vIvB596, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_9, g15_18, g15_19, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g16_11 : reg n16 a1 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, p2vIvB596, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_9, g15_18, g15_19, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g16_12 : reg n16 a2 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, p2vIvB596, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_9, g15_18, g15_19, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g16_13 : reg n16 a3 = BitVec.ofNat 32 (img% b2sOrder256Address) := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, p2vIvB596, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_9, g15_18, g15_19, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g16_16 : reg n16 a6 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, p2vIvB596, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_9, g15_18, g15_19, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m16]; exact w15_50
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m16]; exact w15_54
  have w16_f80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [m16]; exact w15_f80
  have w16_f84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [m16]; exact w15_f84
  have w16_f88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [m16]; exact w15_f88
  have w16_f8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [m16]; exact w15_f8c
  have w16_f90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [m16]; exact w15_f90
  have w16_f94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [m16]; exact w15_f94
  have w16_f98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [m16]; exact w15_f98
  have w16_f9c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [m16]; exact w15_f9c
  have b16_220 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := by rw [m16]; exact b15_220
  have b16_920 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := by rw [m16]; exact b15_920
  have b16_9a0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m16]; exact b15_9a0
  have b16_ca0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ11a := by rw [m16]; exact b15_ca0
  have b16_cc4 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ11b := by rw [m16]; exact b15_cc4
  have b16_1004 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m16]; exact b15_1004
  have a16_120 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m16]; exact a15_120
  have a16_140 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m16]; exact a15_140
  have a16_160 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m16]; exact a15_160
  have a16_180 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m16]; exact a15_180
  have a16_1a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m16]; exact a15_1a0
  have a16_1c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m16]; exact a15_1c0
  have a16_200 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m16]; exact a15_200
  have a16_900 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m16]; exact a15_900
  have a16_980 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m16]; exact a15_980
  have a16_c80 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m16]; exact a15_c80
  have a16_ca4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m16]; exact a15_ca4
  have a16_fe4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m16]; exact a15_fe4
  clear a15_200 a15_fe4 a15_ca4 a15_c80 a15_980 a15_900 a15_1c0 a15_1a0 a15_180 a15_160 a15_140 a15_120 b15_220 b15_1004 b15_cc4 b15_ca0 b15_9a0 b15_920 w15_f9c w15_f98 w15_f94 w15_f90 w15_f8c w15_f88 w15_f84 w15_f80 w15_54 w15_50 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 s15 X15 K15 P15
  -- 0x5BE: lw
  obtain ⟨n17, d17, u17⟩ := s16.lw E16.self p2v_at_5be (off' := 0x5C0) (by decide)
    (by rw [g16_2, show B + 0x21A0 + 0x54 = B + 0x21A0 + BitVec.ofNat 32 0x54 by p2v_addr]; exact p2v_al F (by decide) (by decide))
  have s17 : St n17.mem P2V n17 0x5C0 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, P2vR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, P2vR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : P2vCode n17.mem := E16.fr F fr17
  have V17 : P2vSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
  have g17_9 : reg n17 (9 : Fin 32) = ulo := by rw [u17.regs, upd_ne (by decide) (by decide), g16_9]
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_10]
  have g17_11 : reg n17 a1 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_11]
  have g17_12 : reg n17 a2 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_12]
  have g17_13 : reg n17 a3 = BitVec.ofNat 32 (img% b2sOrder256Address) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_13]
  have g17_16 : reg n17 a6 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_16]
  have g17_18 : reg n17 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = dlo := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
  have g17_21 : reg n17 (21 : Fin 32) = dhi := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = rem := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = qlo := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g16_2, show B + 0x21A0 + 0x54 = B + 0x21A0 + BitVec.ofNat 32 0x54 by p2v_addr, w16_54]
  have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m17]; exact w16_50
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m17]; exact w16_54
  have w17_f80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [m17]; exact w16_f80
  have w17_f84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [m17]; exact w16_f84
  have w17_f88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [m17]; exact w16_f88
  have w17_f8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [m17]; exact w16_f8c
  have w17_f90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [m17]; exact w16_f90
  have w17_f94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [m17]; exact w16_f94
  have w17_f98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [m17]; exact w16_f98
  have w17_f9c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [m17]; exact w16_f9c
  have b17_220 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := by rw [m17]; exact b16_220
  have b17_920 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := by rw [m17]; exact b16_920
  have b17_9a0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m17]; exact b16_9a0
  have b17_ca0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ11a := by rw [m17]; exact b16_ca0
  have b17_cc4 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ11b := by rw [m17]; exact b16_cc4
  have b17_1004 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m17]; exact b16_1004
  have a17_120 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m17]; exact a16_120
  have a17_140 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m17]; exact a16_140
  have a17_160 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m17]; exact a16_160
  have a17_180 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m17]; exact a16_180
  have a17_1a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m17]; exact a16_1a0
  have a17_1c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m17]; exact a16_1c0
  have a17_200 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m17]; exact a16_200
  have a17_900 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m17]; exact a16_900
  have a17_980 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m17]; exact a16_980
  have a17_c80 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m17]; exact a16_c80
  have a17_ca4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m17]; exact a16_ca4
  have a17_fe4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m17]; exact a16_fe4
  clear a16_fe4 a16_ca4 a16_c80 a16_980 a16_900 a16_200 a16_1c0 a16_1a0 a16_180 a16_160 a16_140 a16_120 b16_1004 b16_cc4 b16_ca0 b16_9a0 b16_920 b16_220 w16_f9c w16_f98 w16_f94 w16_f90 w16_f8c w16_f88 w16_f84 w16_f80 w16_54 w16_50 g16_16 g16_13 g16_12 g16_11 g16_10 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_19 g16_18 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
  -- 0x5C0
  obtain ⟨n18, c18, u18⟩ := s17.block p2vIvB5c0 E17.self p2vIvB5c0_end
    ⟨trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem P2V n18 0x5C2 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock p2vIvB5c0 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
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
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb18, runBlock_reg _ _ _ (8 : Fin 32) s17.zero (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = ulo := by
    rw [rb18, runBlock_reg _ _ _ (9 : Fin 32) s17.zero (by decide), g17_9]
  have g18_10 : reg n18 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb18, runBlock_reg _ _ _ a0 s17.zero (by decide), g17_10]
  have g18_11 : reg n18 a1 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb18, runBlock_reg _ _ _ a1 s17.zero (by decide), g17_11]
  have g18_12 : reg n18 a2 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb18, runBlock_reg _ _ _ a2 s17.zero (by decide), g17_12]
  have g18_13 : reg n18 a3 = BitVec.ofNat 32 (img% b2sOrder256Address) := by
    rw [rb18, runBlock_reg _ _ _ a3 s17.zero (by decide), g17_13]
  have g18_16 : reg n18 a6 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb18, runBlock_reg _ _ _ a6 s17.zero (by decide), g17_16]
  have g18_18 : reg n18 (18 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb18, runBlock_reg _ _ _ (18 : Fin 32) s17.zero (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = dlo := by
    rw [rb18, runBlock_reg _ _ _ (19 : Fin 32) s17.zero (by decide), g17_19]
  have g18_21 : reg n18 (21 : Fin 32) = dhi := by
    rw [rb18, runBlock_reg _ _ _ (21 : Fin 32) s17.zero (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb18, runBlock_reg _ _ _ (22 : Fin 32) s17.zero (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb18, runBlock_reg _ _ _ (23 : Fin 32) s17.zero (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = rem := by
    rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = qlo := by
    rw [rb18, runBlock_reg _ _ _ (25 : Fin 32) s17.zero (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb18, runBlock_reg _ _ _ (27 : Fin 32) s17.zero (by decide), g17_27]
  have g18_14 : reg n18 a4 = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, p2vIvB5c0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_10, g17_11, g17_12, g17_13, g17_16, g17_18, g17_19, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk18 : P2vKeepL B n0.mem n18.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m18]; exact w17_50
  have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m18]; exact w17_54
  have w18_f80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [m18]; exact w17_f80
  have w18_f84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [m18]; exact w17_f84
  have w18_f88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [m18]; exact w17_f88
  have w18_f8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [m18]; exact w17_f8c
  have w18_f90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [m18]; exact w17_f90
  have w18_f94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [m18]; exact w17_f94
  have w18_f98 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [m18]; exact w17_f98
  have w18_f9c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [m18]; exact w17_f9c
  have b18_220 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := by rw [m18]; exact b17_220
  have b18_920 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := by rw [m18]; exact b17_920
  have b18_9a0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m18]; exact b17_9a0
  have b18_ca0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ11a := by rw [m18]; exact b17_ca0
  have b18_cc4 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ11b := by rw [m18]; exact b17_cc4
  have b18_1004 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m18]; exact b17_1004
  have a18_120 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m18]; exact a17_120
  have a18_140 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m18]; exact a17_140
  have a18_160 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m18]; exact a17_160
  have a18_180 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m18]; exact a17_180
  have a18_1a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m18]; exact a17_1a0
  have a18_1c0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m18]; exact a17_1c0
  have a18_200 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m18]; exact a17_200
  have a18_900 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m18]; exact a17_900
  have a18_980 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m18]; exact a17_980
  have a18_c80 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m18]; exact a17_c80
  have a18_ca4 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m18]; exact a17_ca4
  have a18_fe4 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m18]; exact a17_fe4
  clear a17_fe4 a17_ca4 a17_c80 a17_980 a17_900 a17_200 a17_1c0 a17_1a0 a17_180 a17_160 a17_140 a17_120 b17_1004 b17_cc4 b17_ca0 b17_9a0 b17_920 b17_220 w17_f9c w17_f98 w17_f94 w17_f90 w17_f8c w17_f88 w17_f84 w17_f80 w17_54 w17_50 g17_8 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_19 g17_18 g17_16 g17_13 g17_12 g17_11 g17_10 g17_9 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0x5C2: lw
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self p2v_at_5c2 (off' := 0x5C4) (by decide)
    (by rw [g18_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by p2v_addr]; exact p2v_al F (by decide) (by decide))
  have s19 : St n19.mem P2V n19 0x5C4 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, P2vR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, P2vR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : P2vCode n19.mem := E18.fr F fr19
  have V19 : P2vSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_8]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_10]
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_11]
  have g19_12 : reg n19 a2 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_12]
  have g19_13 : reg n19 a3 = BitVec.ofNat 32 (img% b2sOrder256Address) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_13]
  have g19_14 : reg n19 a4 = BitVec.ofNat 32 0x11FF43B1 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_14]
  have g19_16 : reg n19 a6 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_16]
  have g19_18 : reg n19 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = dlo := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_21 : reg n19 (21 : Fin 32) = dhi := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = rem := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = qlo := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_9 : reg n19 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by p2v_addr, w18_50]
  have keep_kk19 : P2vKeepL B n0.mem n19.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m19]; exact w18_50
  have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m19]; exact w18_54
  have w19_f80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [m19]; exact w18_f80
  have w19_f84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [m19]; exact w18_f84
  have w19_f88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [m19]; exact w18_f88
  have w19_f8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [m19]; exact w18_f8c
  have w19_f90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [m19]; exact w18_f90
  have w19_f94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [m19]; exact w18_f94
  have w19_f98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [m19]; exact w18_f98
  have w19_f9c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [m19]; exact w18_f9c
  have b19_220 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := by rw [m19]; exact b18_220
  have b19_920 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := by rw [m19]; exact b18_920
  have b19_9a0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m19]; exact b18_9a0
  have b19_ca0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ11a := by rw [m19]; exact b18_ca0
  have b19_cc4 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ11b := by rw [m19]; exact b18_cc4
  have b19_1004 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m19]; exact b18_1004
  have a19_120 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m19]; exact a18_120
  have a19_140 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m19]; exact a18_140
  have a19_160 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m19]; exact a18_160
  have a19_180 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m19]; exact a18_180
  have a19_1a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m19]; exact a18_1a0
  have a19_1c0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m19]; exact a18_1c0
  have a19_200 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_200
  have a19_900 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_900
  have a19_980 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m19]; exact a18_980
  have a19_c80 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_c80
  have a19_ca4 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_ca4
  have a19_fe4 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m19]; exact a18_fe4
  clear a18_fe4 a18_ca4 a18_c80 a18_980 a18_900 a18_200 a18_1c0 a18_1a0 a18_180 a18_160 a18_140 a18_120 b18_1004 b18_cc4 b18_ca0 b18_9a0 b18_920 b18_220 w18_f9c w18_f98 w18_f94 w18_f90 w18_f8c w18_f88 w18_f84 w18_f80 w18_54 w18_50 g18_14 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_19 g18_18 g18_16 g18_13 g18_12 g18_11 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  -- 0x5C4
  obtain ⟨n20, c20, u20⟩ := s19.block p2vIvB5c4 E19.self p2vIvB5c4_end
    ⟨trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem P2V n20 0x5C8 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock p2vIvB5c4 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb20, runBlock_reg _ _ _ a0 s19.zero (by decide), g19_10]
  have g20_11 : reg n20 a1 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb20, runBlock_reg _ _ _ a1 s19.zero (by decide), g19_11]
  have g20_12 : reg n20 a2 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb20, runBlock_reg _ _ _ a2 s19.zero (by decide), g19_12]
  have g20_13 : reg n20 a3 = BitVec.ofNat 32 (img% b2sOrder256Address) := by
    rw [rb20, runBlock_reg _ _ _ a3 s19.zero (by decide), g19_13]
  have g20_14 : reg n20 a4 = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb20, runBlock_reg _ _ _ a4 s19.zero (by decide), g19_14]
  have g20_16 : reg n20 a6 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb20, runBlock_reg _ _ _ a6 s19.zero (by decide), g19_16]
  have g20_18 : reg n20 (18 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = dlo := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_21 : reg n20 (21 : Fin 32) = dhi := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = rem := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = qlo := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_15 : reg n20 a5 = BitVec.ofNat 32 0x332E3755 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, p2vIvB5c4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_11, g19_12, g19_13, g19_14, g19_16, g19_18, g19_19, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g20_17 : reg n20 a7 = BitVec.ofNat 32 ns := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, p2vIvB5c4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_11, g19_12, g19_13, g19_14, g19_16, g19_18, g19_19, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk20 : P2vKeepL B n0.mem n20.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m20]; exact w19_50
  have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m20]; exact w19_54
  have w20_f80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [m20]; exact w19_f80
  have w20_f84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [m20]; exact w19_f84
  have w20_f88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [m20]; exact w19_f88
  have w20_f8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [m20]; exact w19_f8c
  have w20_f90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [m20]; exact w19_f90
  have w20_f94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [m20]; exact w19_f94
  have w20_f98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [m20]; exact w19_f98
  have w20_f9c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [m20]; exact w19_f9c
  have b20_220 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := by rw [m20]; exact b19_220
  have b20_920 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := by rw [m20]; exact b19_920
  have b20_9a0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m20]; exact b19_9a0
  have b20_ca0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ11a := by rw [m20]; exact b19_ca0
  have b20_cc4 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ11b := by rw [m20]; exact b19_cc4
  have b20_1004 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m20]; exact b19_1004
  have a20_120 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m20]; exact a19_120
  have a20_140 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m20]; exact a19_140
  have a20_160 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m20]; exact a19_160
  have a20_180 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m20]; exact a19_180
  have a20_1a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m20]; exact a19_1a0
  have a20_1c0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m20]; exact a19_1c0
  have a20_200 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m20]; exact a19_200
  have a20_900 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m20]; exact a19_900
  have a20_980 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m20]; exact a19_980
  have a20_c80 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m20]; exact a19_c80
  have a20_ca4 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m20]; exact a19_ca4
  have a20_fe4 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m20]; exact a19_fe4
  clear a19_fe4 a19_ca4 a19_c80 a19_980 a19_900 a19_200 a19_1c0 a19_1a0 a19_180 a19_160 a19_140 a19_120 b19_1004 b19_cc4 b19_ca0 b19_9a0 b19_920 b19_220 w19_f9c w19_f98 w19_f94 w19_f90 w19_f8c w19_f88 w19_f84 w19_f80 w19_54 w19_50 g19_9 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_19 g19_18 g19_16 g19_14 g19_13 g19_12 g19_11 g19_10 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x5C8: p2v_ude8F
  obtain ⟨n21, c21, s21, sp21, rk21, R1_21, R2_21, K21, fr21⟩ := p2v_ude8F (co := 0xC80) (ca := 0xFE4) (cb := 0x980) (ct := 0xF80) (s := ns)
    F E20 (UC0.p2v F fR20) s20 p2v_at_5c8 p2v_at_5cc (by decide) (by decide) g20_2
    g20_10 g20_11 g20_12 g20_13 g20_14 g20_15 g20_16 g20_17 hns1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [show 0xFE4 + 0x20 = 0x1004 from rfl, b20_1004]; exact hds)
    (by rw [show 0x980 + 0x20 = 0x9A0 from rfl, b20_9a0]; exact hes)
  obtain ⟨σ21a, A21a, hσ0_21, e0_21, bb0_21, vv0_21⟩ := R1_21
  simp only [p2vI, p2vM, show 0xFE4 + 0x20 = 0x1004 from rfl, show 0x980 + 0x20 = 0x9A0 from rfl,
    show 0xF80 + 0x0 = 0xF80 from rfl, show 0xF80 + 0x8 = 0xF88 from rfl] at e0_21
  rw [b20_1004, a20_fe4, b20_9a0, a20_980,
    acc2_frame w20_f80 w20_f84, acc2_frame w20_f88 w20_f8c] at e0_21
  obtain ⟨σ21b, A21b, hσ1_21, e1_21, bb1_21, vv1_21⟩ := R2_21
  simp only [p2vI, p2vM, show 0xFE4 + 0x20 = 0x1004 from rfl, show 0x980 + 0x20 = 0x9A0 from rfl,
    show 0xF80 + 0x10 = 0xF90 from rfl, show 0xF80 + 0x18 = 0xF98 from rfl] at e1_21
  rw [b20_1004, a20_fe4, b20_9a0, a20_980,
    acc2_frame w20_f90 w20_f94, acc2_frame w20_f98 w20_f9c] at e1_21
  rw [accV_dataR F fR20 (by decide) (by decide)] at bb0_21 vv0_21 bb1_21 vv1_21
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, P2vR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : P2vCode n21.mem := E20.fr F fr21
  have V21 : P2vSaves B n21.mem v := V20.keepL K21 (by decide)
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk21 (3 : Fin 32) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk21 (4 : Fin 32) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [rk21 (8 : Fin 32) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [rk21 (9 : Fin 32) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [rk21 (18 : Fin 32) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = dlo := by rw [rk21 (19 : Fin 32) (by decide), g20_19]
  have g21_21 : reg n21 (21 : Fin 32) = dhi := by rw [rk21 (21 : Fin 32) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk21 (22 : Fin 32) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rk21 (23 : Fin 32) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = rem := by rw [rk21 (24 : Fin 32) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = qlo := by rw [rk21 (25 : Fin 32) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk21 (26 : Fin 32) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk21 (27 : Fin 32) (by decide), g20_27]
  have g21_2 : reg n21 sp = B + 0x21A0 := sp21
  have keep_kk21 : P2vKeepL B n0.mem n21.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24), (0xC80, 0x45)] := keep_kk20.trans K21
  clear keep_kk20
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K21.w32 (by decide) (by decide)).trans w20_50
  have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K21.w32 (by decide) (by decide)).trans w20_54
  have w21_f80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K21.w32 (by decide) (by decide)).trans w20_f80
  have w21_f84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K21.w32 (by decide) (by decide)).trans w20_f84
  have w21_f88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := (K21.w32 (by decide) (by decide)).trans w20_f88
  have w21_f8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := (K21.w32 (by decide) (by decide)).trans w20_f8c
  have w21_f90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := (K21.w32 (by decide) (by decide)).trans w20_f90
  have w21_f94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := (K21.w32 (by decide) (by decide)).trans w20_f94
  have w21_f98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := (K21.w32 (by decide) (by decide)).trans w20_f98
  have w21_f9c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := (K21.w32 (by decide) (by decide)).trans w20_f9c
  have b21_220 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := (K21.b8 (by decide) (by decide)).trans b20_220
  have b21_920 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := (K21.b8 (by decide) (by decide)).trans b20_920
  have b21_9a0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K21.b8 (by decide) (by decide)).trans b20_9a0
  have b21_1004 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K21.b8 (by decide) (by decide)).trans b20_1004
  have a21_120 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K21.acc (by decide) (by decide)).trans a20_120
  have a21_140 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K21.acc (by decide) (by decide)).trans a20_140
  have a21_160 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K21.acc (by decide) (by decide)).trans a20_160
  have a21_180 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K21.acc (by decide) (by decide)).trans a20_180
  have a21_1a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K21.acc (by decide) (by decide)).trans a20_1a0
  have a21_1c0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K21.acc (by decide) (by decide)).trans a20_1c0
  have a21_200 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := (K21.acc (by decide) (by decide)).trans a20_200
  have a21_900 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := (K21.acc (by decide) (by decide)).trans a20_900
  have a21_980 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K21.acc (by decide) (by decide)).trans a20_980
  have a21_fe4 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K21.acc (by decide) (by decide)).trans a20_fe4
  have a21_c80 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := vv0_21
  have a21_ca4 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := vv1_21
  have b21_ca0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := byte_of_toNat bb0_21
  have b21_cc4 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := byte_of_toNat bb1_21
  clear a20_fe4 a20_ca4 a20_c80 a20_980 a20_900 a20_200 a20_1c0 a20_1a0 a20_180 a20_160 a20_140 a20_120 b20_1004 b20_cc4 b20_ca0 b20_9a0 b20_920 b20_220 w20_f9c w20_f98 w20_f94 w20_f90 w20_f8c w20_f88 w20_f84 w20_f80 w20_54 w20_50 g20_17 g20_15 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_16 g20_14 g20_13 g20_12 g20_11 g20_10 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x5D0
  obtain ⟨n22, c22, u22⟩ := s21.block p2vIvB5d0 E21.self p2vIvB5d0_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem P2V n22 0x5E4 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock p2vIvB5d0 (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
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
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb22, runBlock_reg _ _ _ (8 : Fin 32) s21.zero (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [rb22, runBlock_reg _ _ _ (9 : Fin 32) s21.zero (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = dlo := by
    rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
  have g22_21 : reg n22 (21 : Fin 32) = dhi := by
    rw [rb22, runBlock_reg _ _ _ (21 : Fin 32) s21.zero (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb22, runBlock_reg _ _ _ (22 : Fin 32) s21.zero (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb22, runBlock_reg _ _ _ (23 : Fin 32) s21.zero (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = rem := by
    rw [rb22, runBlock_reg _ _ _ (24 : Fin 32) s21.zero (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = qlo := by
    rw [rb22, runBlock_reg _ _ _ (25 : Fin 32) s21.zero (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_10 : reg n22 a0 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, p2vIvB5d0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_18, g21_19, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g22_11 : reg n22 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, p2vIvB5d0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_18, g21_19, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g22_12 : reg n22 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, p2vIvB5d0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_18, g21_19, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk22 : P2vKeepL B n0.mem n22.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24), (0xC80, 0x45)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m22]; exact w21_50
  have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m22]; exact w21_54
  have w22_f80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [m22]; exact w21_f80
  have w22_f84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [m22]; exact w21_f84
  have w22_f88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [m22]; exact w21_f88
  have w22_f8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [m22]; exact w21_f8c
  have w22_f90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [m22]; exact w21_f90
  have w22_f94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [m22]; exact w21_f94
  have w22_f98 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [m22]; exact w21_f98
  have w22_f9c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [m22]; exact w21_f9c
  have b22_220 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := by rw [m22]; exact b21_220
  have b22_920 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := by rw [m22]; exact b21_920
  have b22_9a0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m22]; exact b21_9a0
  have b22_ca0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := by rw [m22]; exact b21_ca0
  have b22_cc4 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := by rw [m22]; exact b21_cc4
  have b22_1004 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m22]; exact b21_1004
  have a22_120 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m22]; exact a21_120
  have a22_140 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m22]; exact a21_140
  have a22_160 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m22]; exact a21_160
  have a22_180 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m22]; exact a21_180
  have a22_1a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m22]; exact a21_1a0
  have a22_1c0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m22]; exact a21_1c0
  have a22_200 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m22]; exact a21_200
  have a22_900 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m22]; exact a21_900
  have a22_980 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m22]; exact a21_980
  have a22_c80 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := by rw [m22]; exact a21_c80
  have a22_ca4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := by rw [m22]; exact a21_ca4
  have a22_fe4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m22]; exact a21_fe4
  clear b21_cc4 b21_ca0 a21_ca4 a21_c80 a21_fe4 a21_980 a21_900 a21_200 a21_1c0 a21_1a0 a21_180 a21_160 a21_140 a21_120 b21_1004 b21_9a0 b21_920 b21_220 w21_f9c w21_f98 w21_f94 w21_f90 w21_f8c w21_f88 w21_f84 w21_f80 w21_54 w21_50 g21_2 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 V21 E21 fR21 t21 vv1_21 bb1_21 vv0_21 bb0_21 fr21 K21 rk21 sp21 s21 c21
  -- 0x5E4: memcpy
  obtain ⟨n23, P23, K23, X23⟩ := p2v_mc (c := 0xFE4) (d := 0xC80) (N := 0x24) F E22 s22 p2v_at_5e4 p2v_at_5e8
    (by decide) (by decide) g22_2 g22_10 g22_11 g22_12
    (by decide) (by decide) (by decide)
  have s23 := P23.st
  have fr23 := P23.fr
  have t23 : Steps n0 n23 := t22.trans P23.steps
  have fR23 : ∀ x, P2vR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : P2vCode n23.mem := E22.fr F fr23
  have V23 : P2vSaves B n23.mem v := V22.keep K23 (by decide)
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [P23.regs sp (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P23.regs (3 : Fin 32) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P23.regs (4 : Fin 32) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [P23.regs (8 : Fin 32) (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [P23.regs (9 : Fin 32) (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [P23.regs (18 : Fin 32) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = dlo := by rw [P23.regs (19 : Fin 32) (by decide), g22_19]
  have g23_21 : reg n23 (21 : Fin 32) = dhi := by rw [P23.regs (21 : Fin 32) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P23.regs (22 : Fin 32) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [P23.regs (23 : Fin 32) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = rem := by rw [P23.regs (24 : Fin 32) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = qlo := by rw [P23.regs (25 : Fin 32) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P23.regs (26 : Fin 32) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P23.regs (27 : Fin 32) (by decide), g22_27]
  have keep_kk23 : P2vKeepL B n0.mem n23.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24), (0xC80, 0x45), (0xFE4, 0x24)] := keep_kk22.trans K23.toL
  clear keep_kk22
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K23.w32 (by decide) (by decide)).trans w22_50
  have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K23.w32 (by decide) (by decide)).trans w22_54
  have w23_f80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K23.w32 (by decide) (by decide)).trans w22_f80
  have w23_f84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K23.w32 (by decide) (by decide)).trans w22_f84
  have w23_f88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := (K23.w32 (by decide) (by decide)).trans w22_f88
  have w23_f8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := (K23.w32 (by decide) (by decide)).trans w22_f8c
  have w23_f90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := (K23.w32 (by decide) (by decide)).trans w22_f90
  have w23_f94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := (K23.w32 (by decide) (by decide)).trans w22_f94
  have w23_f98 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := (K23.w32 (by decide) (by decide)).trans w22_f98
  have w23_f9c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := (K23.w32 (by decide) (by decide)).trans w22_f9c
  have b23_220 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := (K23.b8 (by decide) (by decide)).trans b22_220
  have b23_920 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := (K23.b8 (by decide) (by decide)).trans b22_920
  have b23_9a0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K23.b8 (by decide) (by decide)).trans b22_9a0
  have b23_ca0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := (K23.b8 (by decide) (by decide)).trans b22_ca0
  have b23_cc4 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := (K23.b8 (by decide) (by decide)).trans b22_cc4
  have b23_1004 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := by rw [show 0x1004 = 0xFE4 + 0x20 from rfl, X23 0x20 (by decide)]; exact b22_ca0
  have a23_120 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K23.acc (by decide) (by decide)).trans a22_120
  have a23_140 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K23.acc (by decide) (by decide)).trans a22_140
  have a23_160 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K23.acc (by decide) (by decide)).trans a22_160
  have a23_180 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K23.acc (by decide) (by decide)).trans a22_180
  have a23_1a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K23.acc (by decide) (by decide)).trans a22_1a0
  have a23_1c0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K23.acc (by decide) (by decide)).trans a22_1c0
  have a23_200 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := (K23.acc (by decide) (by decide)).trans a22_200
  have a23_900 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := (K23.acc (by decide) (by decide)).trans a22_900
  have a23_980 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := (K23.acc (by decide) (by decide)).trans a22_980
  have a23_c80 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := (K23.acc (by decide) (by decide)).trans a22_c80
  have a23_ca4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := (K23.acc (by decide) (by decide)).trans a22_ca4
  have a23_fe4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := (accV_S 8 fun q hq => by
    rw [show 0xFE4 + q = 0xFE4 + (0x0 + q) by omega, X23 (0x0 + q) (by omega),
      show 0xC80 + (0x0 + q) = 0xC80 + q by omega]).trans a22_c80
  clear a22_fe4 a22_ca4 a22_c80 a22_980 a22_900 a22_200 a22_1c0 a22_1a0 a22_180 a22_160 a22_140 a22_120 b22_1004 b22_cc4 b22_ca0 b22_9a0 b22_920 b22_220 w22_f9c w22_f98 w22_f94 w22_f90 w22_f8c w22_f88 w22_f84 w22_f80 w22_54 w22_50 g22_12 g22_11 g22_10 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  -- 0x5EC
  obtain ⟨n24, c24, u24⟩ := s23.block p2vIvB5ec E23.self p2vIvB5ec_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem P2V n24 0x600 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock p2vIvB5ec (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = dlo := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_21 : reg n24 (21 : Fin 32) = dhi := by
    rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = rem := by
    rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = qlo := by
    rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_10 : reg n24 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, p2vIvB5ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_19, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g24_11 : reg n24 a1 = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, p2vIvB5ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_19, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g24_12 : reg n24 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, p2vIvB5ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_19, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk24 : P2vKeepL B n0.mem n24.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24), (0xC80, 0x45), (0xFE4, 0x24)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m24]; exact w23_50
  have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m24]; exact w23_54
  have w24_f80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [m24]; exact w23_f80
  have w24_f84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [m24]; exact w23_f84
  have w24_f88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [m24]; exact w23_f88
  have w24_f8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [m24]; exact w23_f8c
  have w24_f90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [m24]; exact w23_f90
  have w24_f94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [m24]; exact w23_f94
  have w24_f98 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [m24]; exact w23_f98
  have w24_f9c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [m24]; exact w23_f9c
  have b24_220 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := by rw [m24]; exact b23_220
  have b24_920 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := by rw [m24]; exact b23_920
  have b24_9a0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m24]; exact b23_9a0
  have b24_ca0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := by rw [m24]; exact b23_ca0
  have b24_cc4 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := by rw [m24]; exact b23_cc4
  have b24_1004 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := by rw [m24]; exact b23_1004
  have a24_120 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m24]; exact a23_120
  have a24_140 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m24]; exact a23_140
  have a24_160 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m24]; exact a23_160
  have a24_180 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m24]; exact a23_180
  have a24_1a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m24]; exact a23_1a0
  have a24_1c0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m24]; exact a23_1c0
  have a24_200 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m24]; exact a23_200
  have a24_900 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m24]; exact a23_900
  have a24_980 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = ev := by rw [m24]; exact a23_980
  have a24_c80 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := by rw [m24]; exact a23_c80
  have a24_ca4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := by rw [m24]; exact a23_ca4
  have a24_fe4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := by rw [m24]; exact a23_fe4
  clear a23_fe4 a23_ca4 a23_c80 a23_980 a23_900 a23_200 a23_1c0 a23_1a0 a23_180 a23_160 a23_140 a23_120 b23_1004 b23_cc4 b23_ca0 b23_9a0 b23_920 b23_220 w23_f9c w23_f98 w23_f94 w23_f90 w23_f8c w23_f88 w23_f84 w23_f80 w23_54 w23_50 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_19 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 s23 X23 K23 P23
  -- 0x600: memcpy
  obtain ⟨n25, P25, K25, X25⟩ := p2v_mc (c := 0x980) (d := 0xCA4) (N := 0x24) F E24 s24 p2v_at_600 p2v_at_604
    (by decide) (by decide) g24_2 g24_10 g24_11 g24_12
    (by decide) (by decide) (by decide)
  have s25 := P25.st
  have fr25 := P25.fr
  have t25 : Steps n0 n25 := t24.trans P25.steps
  have fR25 : ∀ x, P2vR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : P2vCode n25.mem := E24.fr F fr25
  have V25 : P2vSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [P25.regs sp (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P25.regs (3 : Fin 32) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P25.regs (4 : Fin 32) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by rw [P25.regs (8 : Fin 32) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by rw [P25.regs (9 : Fin 32) (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = BitVec.ofNat 32 ns := by rw [P25.regs (18 : Fin 32) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = dlo := by rw [P25.regs (19 : Fin 32) (by decide), g24_19]
  have g25_21 : reg n25 (21 : Fin 32) = dhi := by rw [P25.regs (21 : Fin 32) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P25.regs (22 : Fin 32) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [P25.regs (23 : Fin 32) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = rem := by rw [P25.regs (24 : Fin 32) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = qlo := by rw [P25.regs (25 : Fin 32) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P25.regs (26 : Fin 32) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P25.regs (27 : Fin 32) (by decide), g24_27]
  have keep_kk25 : P2vKeepL B n0.mem n25.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24), (0xC80, 0x45), (0xFE4, 0x24), (0x980, 0x24)] := keep_kk24.trans K25.toL
  clear keep_kk24
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := (K25.w32 (by decide) (by decide)).trans w24_50
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := (K25.w32 (by decide) (by decide)).trans w24_54
  have w25_f80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := (K25.w32 (by decide) (by decide)).trans w24_f80
  have w25_f84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := (K25.w32 (by decide) (by decide)).trans w24_f84
  have w25_f88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := (K25.w32 (by decide) (by decide)).trans w24_f88
  have w25_f8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := (K25.w32 (by decide) (by decide)).trans w24_f8c
  have w25_f90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := (K25.w32 (by decide) (by decide)).trans w24_f90
  have w25_f94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := (K25.w32 (by decide) (by decide)).trans w24_f94
  have w25_f98 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := (K25.w32 (by decide) (by decide)).trans w24_f98
  have w25_f9c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := (K25.w32 (by decide) (by decide)).trans w24_f9c
  have b25_220 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := (K25.b8 (by decide) (by decide)).trans b24_220
  have b25_920 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := (K25.b8 (by decide) (by decide)).trans b24_920
  have b25_ca0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := (K25.b8 (by decide) (by decide)).trans b24_ca0
  have b25_cc4 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := (K25.b8 (by decide) (by decide)).trans b24_cc4
  have b25_1004 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := (K25.b8 (by decide) (by decide)).trans b24_1004
  have b25_9a0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = BitVec.ofNat 8 (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := by rw [show 0x9A0 = 0x980 + 0x20 from rfl, X25 0x20 (by decide)]; exact b24_cc4
  have a25_120 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K25.acc (by decide) (by decide)).trans a24_120
  have a25_140 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K25.acc (by decide) (by decide)).trans a24_140
  have a25_160 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K25.acc (by decide) (by decide)).trans a24_160
  have a25_180 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K25.acc (by decide) (by decide)).trans a24_180
  have a25_1a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K25.acc (by decide) (by decide)).trans a24_1a0
  have a25_1c0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K25.acc (by decide) (by decide)).trans a24_1c0
  have a25_200 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := (K25.acc (by decide) (by decide)).trans a24_200
  have a25_900 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := (K25.acc (by decide) (by decide)).trans a24_900
  have a25_c80 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := (K25.acc (by decide) (by decide)).trans a24_c80
  have a25_ca4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := (K25.acc (by decide) (by decide)).trans a24_ca4
  have a25_fe4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := (K25.acc (by decide) (by decide)).trans a24_fe4
  have a25_980 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := (accV_S 8 fun q hq => by
    rw [show 0x980 + q = 0x980 + (0x0 + q) by omega, X25 (0x0 + q) (by omega),
      show 0xCA4 + (0x0 + q) = 0xCA4 + q by omega]).trans a24_ca4
  clear a24_fe4 a24_ca4 a24_c80 a24_980 a24_900 a24_200 a24_1c0 a24_1a0 a24_180 a24_160 a24_140 a24_120 b24_1004 b24_cc4 b24_ca0 b24_9a0 b24_920 b24_220 w24_f9c w24_f98 w24_f94 w24_f90 w24_f8c w24_f88 w24_f84 w24_f80 w24_54 w24_50 g24_12 g24_11 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0x608
  obtain ⟨n26, c26, u26⟩ := s25.block p2vIvB608 E25.self p2vIvB608_end
    ⟨trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem P2V n26 0x60C (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock p2vIvB608 (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
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
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = dlo := by
    rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
  have g26_21 : reg n26 (21 : Fin 32) = dhi := by
    rw [rb26, runBlock_reg _ _ _ (21 : Fin 32) s25.zero (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb26, runBlock_reg _ _ _ (22 : Fin 32) s25.zero (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb26, runBlock_reg _ _ _ (23 : Fin 32) s25.zero (by decide), g25_23]
  have g26_25 : reg n26 (25 : Fin 32) = qlo := by
    rw [rb26, runBlock_reg _ _ _ (25 : Fin 32) s25.zero (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
  have g26_24 : reg n26 (24 : Fin 32) = (rem) - (BitVec.ofNat 32 ns) := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, p2vIvB608, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_18, g25_19, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk26 : P2vKeepL B n0.mem n26.mem [(0xF80, 0x4), (0xF84, 0x4), (0xF88, 0x4), (0xF8C, 0x4), (0xF90, 0x4), (0xF94, 0x4), (0xF98, 0x4), (0xF9C, 0x4), (0xC80, 0x45), (0x900, 0x24), (0x200, 0x24), (0xC80, 0x45), (0xFE4, 0x24), (0x980, 0x24)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x332E3755 := by rw [m26]; exact w25_50
  have w26_54 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 0x11FF43B1 := by rw [m26]; exact w25_54
  have w26_f80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) = ulo := by rw [m26]; exact w25_f80
  have w26_f84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF84) = uhi := by rw [m26]; exact w25_f84
  have w26_f88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF88) = vlo := by rw [m26]; exact w25_f88
  have w26_f8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8C) = vhi := by rw [m26]; exact w25_f8c
  have w26_f90 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF90) = qlo := by rw [m26]; exact w25_f90
  have w26_f94 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF94) = qhi := by rw [m26]; exact w25_f94
  have w26_f98 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF98) = rlo := by rw [m26]; exact w25_f98
  have w26_f9c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF9C) = rhi := by rw [m26]; exact w25_f9c
  have b26_220 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 σ11b := by rw [m26]; exact b25_220
  have b26_920 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ11a := by rw [m26]; exact b25_920
  have b26_9a0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = BitVec.ofNat 8 (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := by rw [m26]; exact b25_9a0
  have b26_ca0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := by rw [m26]; exact b25_ca0
  have b26_cc4 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := by rw [m26]; exact b25_cc4
  have b26_1004 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = BitVec.ofNat 8 (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).1 := by rw [m26]; exact b25_1004
  have a26_120 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m26]; exact a25_120
  have a26_140 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m26]; exact a25_140
  have a26_160 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m26]; exact a25_160
  have a26_180 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m26]; exact a25_180
  have a26_1a0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m26]; exact a25_1a0
  have a26_1c0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m26]; exact a25_1c0
  have a26_200 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = A11b / 2 ^ ns % 2 ^ 256 := by rw [m26]; exact a25_200
  have a26_900 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A11a / 2 ^ ns % 2 ^ 256 := by rw [m26]; exact a25_900
  have a26_980 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := by rw [m26]; exact a25_980
  have a26_c80 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := by rw [m26]; exact a25_c80
  have a26_ca4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ21b A21b ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := by rw [m26]; exact a25_ca4
  have a26_fe4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (lrsm8 σ21a A21a ((BitVec.ofNat 32 0x11FF43B1).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755).toNat) ns (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)).2 := by rw [m26]; exact a25_fe4
  clear a25_980 a25_fe4 a25_ca4 a25_c80 a25_900 a25_200 a25_1c0 a25_1a0 a25_180 a25_160 a25_140 a25_120 b25_9a0 b25_1004 b25_cc4 b25_ca0 b25_920 b25_220 w25_f9c w25_f98 w25_f94 w25_f90 w25_f8c w25_f88 w25_f84 w25_f80 w25_54 w25_50 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 s25 X25 K25 P25
  exact .inr ⟨σ11a, A11a, e0_11, hσ0_11, σ11b, A11b, e1_11, hσ1_11, σ21a, A21a, e0_21, hσ0_21, σ21b, A21b, e1_21, hσ1_21, n26, t26, s26, E26, V26, fR26, g26_2, g26_3, g26_4, g26_8, g26_9, g26_19, g26_21, g26_22, g26_23, g26_24, g26_26, g26_27, w26_50, w26_54, w26_f80, w26_f84, w26_f88, w26_f8c, w26_f90, w26_f94, w26_f98, w26_f9c, b26_220, b26_920, b26_9a0, b26_ca0, b26_cc4, b26_1004, a26_120, a26_140, a26_160, a26_180, a26_1a0, a26_1c0, a26_200, a26_900, a26_980, a26_c80, a26_ca4, a26_fe4, keep_kk26.mono (by decide)⟩

end C3.RV32.P2v
