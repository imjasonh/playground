import C3BootProofs.Proofs.P2vZLib

/-!
# `p256VerifyPrehash`: the end of a batch of the inversion of `Z`

From the divstep loop's exit at 0xE06 to the batch's branch at 0xEFC: the batch's matrix is stored at 0x1318, `update_fg` applies it to `f` and `g` and `update_de` to `d` and `e` modulo the field's modulus at 0x980, and the steps left drop by the batch's size.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vZBe06 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x1EC, .alu .add a0 a0 sp]
theorem p2vZBe06_end : blockEnd p256VerifyPrehashCode 0xE06 p2vZBe06 = some 0xE0E := by
  simp only [p2vZBe06]
  rw [blockEnd, p2v_at_e06]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e08]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e0c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZBe30 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x781, .aluImm .add a2 sp 0x7FF, .aluImm .add a2 a2 0x101, .lui a3 0x1000, .aluImm .add a3 a3 0x318, .alu .add a3 a3 sp]
theorem p2vZBe30_end : blockEnd p256VerifyPrehashCode 0xE30 p2vZBe30 = some 0xE50 := by
  simp only [p2vZBe30]
  rw [blockEnd, p2v_at_e30]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e34]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e38]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e3c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e40]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e44]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e48]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e4a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e4e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZBe52 : List BInstr :=
  [.alu .add a4 x0 (9 : Fin 32)]
theorem p2vZBe52_end : blockEnd p256VerifyPrehashCode 0xE52 p2vZBe52 = some 0xE54 := by
  simp only [p2vZBe52]
  rw [blockEnd, p2v_at_e52]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZBe5c : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x781, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x24]
theorem p2vZBe5c_end : blockEnd p256VerifyPrehashCode 0xE5C p2vZBe5c = some 0xE70 := by
  simp only [p2vZBe5c]
  rw [blockEnd, p2v_at_e5c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e60]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e64]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e68]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e6c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZBe78 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x101, .aluImm .add a2 x0 0x24, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x4A5]
theorem p2vZBe78_end : blockEnd p256VerifyPrehashCode 0xE78 p2vZBe78 = some 0xE8C := by
  simp only [p2vZBe78]
  rw [blockEnd, p2v_at_e78]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e7c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e80]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e84]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e88]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZBe94 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x200, .aluImm .add a2 sp 0x7FF, .aluImm .add a2 a2 0x7E5, .aluImm .add a3 sp 0x7FF, .aluImm .add a3 a3 0x181, .aluImm .add a4 x0 0xFFFFFFFF, .aluImm .add a5 x0 0xFFFFFFFF, .lui a6 0x1000, .aluImm .add a6 a6 0x318, .alu .add a6 a6 sp, .alu .add (17 : Fin 32) x0 (9 : Fin 32)]
theorem p2vZBe94_end : blockEnd p256VerifyPrehashCode 0xE94 p2vZBe94 = some 0xEBC := by
  simp only [p2vZBe94]
  rw [blockEnd, p2v_at_e94]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e98]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e9c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_e9e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ea2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ea6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_eaa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_eae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_eb0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_eb2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_eb4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_eb8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_eba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZBec4 : List BInstr :=
  [.aluImm .add a0 sp 0x200, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x24]
theorem p2vZBec4_end : blockEnd p256VerifyPrehashCode 0xEC4 p2vZBec4 = some 0xED2 := by
  simp only [p2vZBec4]
  rw [blockEnd, p2v_at_ec4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ec6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_eca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ece]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZBeda : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x7E5, .aluImm .add a2 x0 0x24, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x4A5]
theorem p2vZBeda_end : blockEnd p256VerifyPrehashCode 0xEDA p2vZBeda = some 0xEEE := by
  simp only [p2vZBeda]
  rw [blockEnd, p2v_at_eda]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ede]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ee2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ee6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_eea]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZBef6 : List BInstr :=
  [.alu .add a4 x0 (8 : Fin 32)]
theorem p2vZBef6_end : blockEnd p256VerifyPrehashCode 0xEF6 p2vZBef6 = some 0xEF8 := by
  simp only [p2vZBef6]
  rw [blockEnd, p2v_at_ef6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZBefa : List BInstr :=
  [.alu .sub a0 a0 (9 : Fin 32)]
theorem p2vZBefa_end : blockEnd p256VerifyPrehashCode 0xEFA p2vZBefa = some 0xEFC := by
  simp only [p2vZBefa]
  rw [blockEnd, p2v_at_efa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_zb {B dlo dhi rem nzw ulo uhi vlo vhi qlo qhi rlo rhi : Word} {ns : Nat} {fs gs ds es : BitVec 8} {rv X Y fv gv dv ev : Nat} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0xE06 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920)
    (g0_13 : reg n0 a3 = rhi)
    (g0_18 : reg n0 (18 : Fin 32) = qhi)
    (g0_20 : reg n0 (20 : Fin 32) = vlo)
    (g0_22 : reg n0 (22 : Fin 32) = rlo)
    (g0_23 : reg n0 (23 : Fin 32) = ulo)
    (g0_24 : reg n0 (24 : Fin 32) = dhi)
    (g0_25 : reg n0 (25 : Fin 32) = vhi)
    (g0_26 : reg n0 (26 : Fin 32) = uhi)
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw)
    (w0_14 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo)
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
    (UC0 : P2vUpCode M0)
    (hns1 : 1 ≤ ns)
    (hns2 : ns ≤ 62)
    (hfs : fs.toNat ≤ 1)
    (hgs : gs.toNat ≤ 1)
    (hds : ds.toNat ≤ 1)
    (hes : es.toNat ≤ 1) :
    (¬ (∃ σ14a A14a, sgnVal σ14a A14a = sgnVal (fs).toNat (fv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧ (σ14a ≤ 1) ∧ ∃ σ14b A14b, sgnVal σ14b A14b = sgnVal (fs).toNat (fv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧ (σ14b ≤ 1) ∧ ∃ σ20a A20a, sgnVal σ20a A20a = sgnVal (ds).toNat (dv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧ (σ20a ≤ 1) ∧ ∃ σ20b A20b, sgnVal σ20b A20b = sgnVal (ds).toNat (dv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧ (σ20b ≤ 1) ∧ True) ∧ P2vRet B v n0 0) ∨
    (∃ σ14a A14a, sgnVal σ14a A14a = sgnVal (fs).toNat (fv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧
    (σ14a ≤ 1) ∧
    ∃ σ14b A14b, sgnVal σ14b A14b = sgnVal (fs).toNat (fv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧
    (σ14b ≤ 1) ∧
    ∃ σ20a A20a, sgnVal σ20a A20a = sgnVal (ds).toNat (dv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧
    (σ20a ≤ 1) ∧
    ∃ σ20b A20b, sgnVal σ20b A20b = sgnVal (ds).toNat (dv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧
    (σ20b ≤ 1) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0xEFC (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' a0 = (rem) - (BitVec.ofNat 32 ns) ∧
        reg n' a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
        reg n' (24 : Fin 32) = dhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ14b ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A14b / 2 ^ ns % 2 ^ 256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y ∧
        P2vKeepL B n0.mem n'.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24), (0x900, 0x24), (0xC80, 0x45), (0x200, 0x24), (0xFE4, 0x24)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xE06
  obtain ⟨n1, c1, u1⟩ := s0.block p2vZBe06 E0.self p2vZBe06_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem P2V n1 0xE0E (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock p2vZBe06 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_8 : reg n1 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
  have g1_13 : reg n1 a3 = rhi := by
    rw [rb1, runBlock_reg _ _ _ a3 s0.zero (by decide), g0_13]
  have g1_18 : reg n1 (18 : Fin 32) = qhi := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_20 : reg n1 (20 : Fin 32) = vlo := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_22 : reg n1 (22 : Fin 32) = rlo := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = ulo := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = dhi := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = vhi := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = uhi := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vZBe06, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_13, g0_18, g0_20, g0_22, g0_23, g0_24, g0_25, g0_26, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  have w1_10 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m1]; exact w0_10
  have w1_14 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m1]; exact w0_14
  have w1_18 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m1]; exact w0_18
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m1]; exact w0_40
  have w1_54 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m1]; exact w0_54
  have b1_220 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m1]; exact b0_220
  have b1_920 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m1]; exact b0_920
  have b1_fa0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m1]; exact b0_fa0
  have b1_1004 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m1]; exact b0_1004
  have a1_180 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m1]; exact a0_180
  have a1_200 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m1]; exact a0_200
  have a1_900 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m1]; exact a0_900
  have a1_980 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m1]; exact a0_980
  have a1_f80 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m1]; exact a0_f80
  have a1_fe4 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m1]; exact a0_fe4
  have a1_1338 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m1]; exact a0_1338
  have a1_1358 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m1]; exact a0_1358
  -- 0xE0E: sw
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := p2v_sw F E1 s1 p2v_at_e0e (off' := 0xE12) (c := 0x1318)
    (by decide) (by rw [g1_10]; p2v_addr) (by decide) (by decide)
  have t2 : Steps n0 n2 := t1.trans d2
  have fR2 : ∀ x, P2vR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : P2vCode n2.mem := E1.fr F fr2
  have V2 : P2vSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rg2 sp, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg2 (3 : Fin 32), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg2 (4 : Fin 32), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg2 (8 : Fin 32), g1_8]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by rw [rg2 a0, g1_10]
  have g2_13 : reg n2 a3 = rhi := by rw [rg2 a3, g1_13]
  have g2_18 : reg n2 (18 : Fin 32) = qhi := by rw [rg2 (18 : Fin 32), g1_18]
  have g2_20 : reg n2 (20 : Fin 32) = vlo := by rw [rg2 (20 : Fin 32), g1_20]
  have g2_22 : reg n2 (22 : Fin 32) = rlo := by rw [rg2 (22 : Fin 32), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = ulo := by rw [rg2 (23 : Fin 32), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = dhi := by rw [rg2 (24 : Fin 32), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = vhi := by rw [rg2 (25 : Fin 32), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = uhi := by rw [rg2 (26 : Fin 32), g1_26]
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [(0x1318, 0x4)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have w2_10 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K2.w32 (by decide) (by decide)).trans w1_10
  have w2_14 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K2.w32 (by decide) (by decide)).trans w1_14
  have w2_18 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K2.w32 (by decide) (by decide)).trans w1_18
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K2.w32 (by decide) (by decide)).trans w1_40
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K2.w32 (by decide) (by decide)).trans w1_54
  have b2_220 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K2.b8 (by decide) (by decide)).trans b1_220
  have b2_920 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K2.b8 (by decide) (by decide)).trans b1_920
  have b2_fa0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K2.b8 (by decide) (by decide)).trans b1_fa0
  have b2_1004 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K2.b8 (by decide) (by decide)).trans b1_1004
  have w2_1318 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [W2, g1_23]
  have a2_180 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K2.acc (by decide) (by decide)).trans a1_180
  have a2_200 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K2.acc (by decide) (by decide)).trans a1_200
  have a2_900 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K2.acc (by decide) (by decide)).trans a1_900
  have a2_980 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K2.acc (by decide) (by decide)).trans a1_980
  have a2_f80 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K2.acc (by decide) (by decide)).trans a1_f80
  have a2_fe4 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K2.acc (by decide) (by decide)).trans a1_fe4
  have a2_1338 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K2.acc (by decide) (by decide)).trans a1_1338
  have a2_1358 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K2.acc (by decide) (by decide)).trans a1_1358
  clear a1_1358 a1_1338 a1_fe4 a1_f80 a1_980 a1_900 a1_200 a1_180 b1_1004 b1_fa0 b1_920 b1_220 w1_54 w1_40 w1_18 w1_14 w1_10 g1_10 g1_26 g1_25 g1_24 g1_23 g1_22 g1_20 g1_18 g1_13 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0xE12: sw
  obtain ⟨n3, d3, s3, fr3, K3, W3, rg3⟩ := p2v_sw F E2 s2 p2v_at_e12 (off' := 0xE16) (c := 0x131C)
    (by decide) (by rw [g2_10]; p2v_addr) (by decide) (by decide)
  have t3 : Steps n0 n3 := t2.trans d3
  have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : P2vCode n3.mem := E2.fr F fr3
  have V3 : P2vSaves B n3.mem v := V2.keep K3 (by decide)
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [rg3 sp, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg3 (3 : Fin 32), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg3 (4 : Fin 32), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg3 (8 : Fin 32), g2_8]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by rw [rg3 a0, g2_10]
  have g3_13 : reg n3 a3 = rhi := by rw [rg3 a3, g2_13]
  have g3_18 : reg n3 (18 : Fin 32) = qhi := by rw [rg3 (18 : Fin 32), g2_18]
  have g3_20 : reg n3 (20 : Fin 32) = vlo := by rw [rg3 (20 : Fin 32), g2_20]
  have g3_22 : reg n3 (22 : Fin 32) = rlo := by rw [rg3 (22 : Fin 32), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = ulo := by rw [rg3 (23 : Fin 32), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = dhi := by rw [rg3 (24 : Fin 32), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = vhi := by rw [rg3 (25 : Fin 32), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = uhi := by rw [rg3 (26 : Fin 32), g2_26]
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0x1318, 0x4), (0x131C, 0x4)] := keep_kk2.trans K3.toL
  clear keep_kk2
  have w3_10 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K3.w32 (by decide) (by decide)).trans w2_10
  have w3_14 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K3.w32 (by decide) (by decide)).trans w2_14
  have w3_18 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K3.w32 (by decide) (by decide)).trans w2_18
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K3.w32 (by decide) (by decide)).trans w2_40
  have w3_54 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K3.w32 (by decide) (by decide)).trans w2_54
  have w3_1318 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K3.w32 (by decide) (by decide)).trans w2_1318
  have b3_220 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K3.b8 (by decide) (by decide)).trans b2_220
  have b3_920 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K3.b8 (by decide) (by decide)).trans b2_920
  have b3_fa0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K3.b8 (by decide) (by decide)).trans b2_fa0
  have b3_1004 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K3.b8 (by decide) (by decide)).trans b2_1004
  have w3_131c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [W3, g2_26]
  have a3_180 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K3.acc (by decide) (by decide)).trans a2_180
  have a3_200 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K3.acc (by decide) (by decide)).trans a2_200
  have a3_900 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K3.acc (by decide) (by decide)).trans a2_900
  have a3_980 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K3.acc (by decide) (by decide)).trans a2_980
  have a3_f80 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K3.acc (by decide) (by decide)).trans a2_f80
  have a3_fe4 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K3.acc (by decide) (by decide)).trans a2_fe4
  have a3_1338 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K3.acc (by decide) (by decide)).trans a2_1338
  have a3_1358 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K3.acc (by decide) (by decide)).trans a2_1358
  clear a2_1358 a2_1338 a2_fe4 a2_f80 a2_980 a2_900 a2_200 a2_180 w2_1318 b2_1004 b2_fa0 b2_920 b2_220 w2_54 w2_40 w2_18 w2_14 w2_10 g2_26 g2_25 g2_24 g2_23 g2_22 g2_20 g2_18 g2_13 g2_10 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 rg2 W2 K2 fr2 s2 d2
  -- 0xE16: sw
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := p2v_sw F E3 s3 p2v_at_e16 (off' := 0xE1A) (c := 0x1320)
    (by decide) (by rw [g3_10]; p2v_addr) (by decide) (by decide)
  have t4 : Steps n0 n4 := t3.trans d4
  have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : P2vCode n4.mem := E3.fr F fr4
  have V4 : P2vSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rg4 sp, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg4 (3 : Fin 32), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg4 (4 : Fin 32), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg4 (8 : Fin 32), g3_8]
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by rw [rg4 a0, g3_10]
  have g4_13 : reg n4 a3 = rhi := by rw [rg4 a3, g3_13]
  have g4_18 : reg n4 (18 : Fin 32) = qhi := by rw [rg4 (18 : Fin 32), g3_18]
  have g4_20 : reg n4 (20 : Fin 32) = vlo := by rw [rg4 (20 : Fin 32), g3_20]
  have g4_22 : reg n4 (22 : Fin 32) = rlo := by rw [rg4 (22 : Fin 32), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = ulo := by rw [rg4 (23 : Fin 32), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = dhi := by rw [rg4 (24 : Fin 32), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = vhi := by rw [rg4 (25 : Fin 32), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = uhi := by rw [rg4 (26 : Fin 32), g3_26]
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4)] := keep_kk3.trans K4.toL
  clear keep_kk3
  have w4_10 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K4.w32 (by decide) (by decide)).trans w3_10
  have w4_14 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K4.w32 (by decide) (by decide)).trans w3_14
  have w4_18 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K4.w32 (by decide) (by decide)).trans w3_18
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K4.w32 (by decide) (by decide)).trans w3_40
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K4.w32 (by decide) (by decide)).trans w3_54
  have w4_1318 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K4.w32 (by decide) (by decide)).trans w3_1318
  have w4_131c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K4.w32 (by decide) (by decide)).trans w3_131c
  have b4_220 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K4.b8 (by decide) (by decide)).trans b3_220
  have b4_920 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K4.b8 (by decide) (by decide)).trans b3_920
  have b4_fa0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K4.b8 (by decide) (by decide)).trans b3_fa0
  have b4_1004 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K4.b8 (by decide) (by decide)).trans b3_1004
  have w4_1320 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [W4, g3_20]
  have a4_180 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K4.acc (by decide) (by decide)).trans a3_180
  have a4_200 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K4.acc (by decide) (by decide)).trans a3_200
  have a4_900 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K4.acc (by decide) (by decide)).trans a3_900
  have a4_980 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K4.acc (by decide) (by decide)).trans a3_980
  have a4_f80 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K4.acc (by decide) (by decide)).trans a3_f80
  have a4_fe4 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K4.acc (by decide) (by decide)).trans a3_fe4
  have a4_1338 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K4.acc (by decide) (by decide)).trans a3_1338
  have a4_1358 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K4.acc (by decide) (by decide)).trans a3_1358
  clear a3_1358 a3_1338 a3_fe4 a3_f80 a3_980 a3_900 a3_200 a3_180 w3_131c b3_1004 b3_fa0 b3_920 b3_220 w3_1318 w3_54 w3_40 w3_18 w3_14 w3_10 g3_26 g3_25 g3_24 g3_23 g3_22 g3_20 g3_18 g3_13 g3_10 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 rg3 W3 K3 fr3 s3 d3
  -- 0xE1A: sw
  obtain ⟨n5, d5, s5, fr5, K5, W5, rg5⟩ := p2v_sw F E4 s4 p2v_at_e1a (off' := 0xE1E) (c := 0x1324)
    (by decide) (by rw [g4_10]; p2v_addr) (by decide) (by decide)
  have t5 : Steps n0 n5 := t4.trans d5
  have fR5 : ∀ x, P2vR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : P2vCode n5.mem := E4.fr F fr5
  have V5 : P2vSaves B n5.mem v := V4.keep K5 (by decide)
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rg5 sp, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg5 (3 : Fin 32), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg5 (4 : Fin 32), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg5 (8 : Fin 32), g4_8]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by rw [rg5 a0, g4_10]
  have g5_13 : reg n5 a3 = rhi := by rw [rg5 a3, g4_13]
  have g5_18 : reg n5 (18 : Fin 32) = qhi := by rw [rg5 (18 : Fin 32), g4_18]
  have g5_20 : reg n5 (20 : Fin 32) = vlo := by rw [rg5 (20 : Fin 32), g4_20]
  have g5_22 : reg n5 (22 : Fin 32) = rlo := by rw [rg5 (22 : Fin 32), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = ulo := by rw [rg5 (23 : Fin 32), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = dhi := by rw [rg5 (24 : Fin 32), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = vhi := by rw [rg5 (25 : Fin 32), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = uhi := by rw [rg5 (26 : Fin 32), g4_26]
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4)] := keep_kk4.trans K5.toL
  clear keep_kk4
  have w5_10 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K5.w32 (by decide) (by decide)).trans w4_10
  have w5_14 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K5.w32 (by decide) (by decide)).trans w4_14
  have w5_18 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K5.w32 (by decide) (by decide)).trans w4_18
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K5.w32 (by decide) (by decide)).trans w4_40
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K5.w32 (by decide) (by decide)).trans w4_54
  have w5_1318 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K5.w32 (by decide) (by decide)).trans w4_1318
  have w5_131c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K5.w32 (by decide) (by decide)).trans w4_131c
  have w5_1320 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := (K5.w32 (by decide) (by decide)).trans w4_1320
  have b5_220 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K5.b8 (by decide) (by decide)).trans b4_220
  have b5_920 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K5.b8 (by decide) (by decide)).trans b4_920
  have b5_fa0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K5.b8 (by decide) (by decide)).trans b4_fa0
  have b5_1004 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K5.b8 (by decide) (by decide)).trans b4_1004
  have w5_1324 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [W5, g4_25]
  have a5_180 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K5.acc (by decide) (by decide)).trans a4_180
  have a5_200 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K5.acc (by decide) (by decide)).trans a4_200
  have a5_900 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K5.acc (by decide) (by decide)).trans a4_900
  have a5_980 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K5.acc (by decide) (by decide)).trans a4_980
  have a5_f80 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K5.acc (by decide) (by decide)).trans a4_f80
  have a5_fe4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K5.acc (by decide) (by decide)).trans a4_fe4
  have a5_1338 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K5.acc (by decide) (by decide)).trans a4_1338
  have a5_1358 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K5.acc (by decide) (by decide)).trans a4_1358
  clear a4_1358 a4_1338 a4_fe4 a4_f80 a4_980 a4_900 a4_200 a4_180 w4_1320 b4_1004 b4_fa0 b4_920 b4_220 w4_131c w4_1318 w4_54 w4_40 w4_18 w4_14 w4_10 g4_26 g4_25 g4_24 g4_23 g4_22 g4_20 g4_18 g4_13 g4_10 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 rg4 W4 K4 fr4 s4 d4
  -- 0xE1E: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self p2v_at_e1e (off' := 0xE20) (by decide)
    (by rw [g5_2, show B + 0x21A0 + 0x54 = B + 0x21A0 + BitVec.ofNat 32 0x54 by p2v_addr]; exact p2v_al F (by decide) (by decide))
  have s6 : St n6.mem P2V n6 0xE20 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, P2vR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_8]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by rw [u6.regs, upd_ne (by decide) (by decide), g5_10]
  have g6_13 : reg n6 a3 = rhi := by rw [u6.regs, upd_ne (by decide) (by decide), g5_13]
  have g6_18 : reg n6 (18 : Fin 32) = qhi := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_20 : reg n6 (20 : Fin 32) = vlo := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_22 : reg n6 (22 : Fin 32) = rlo := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = ulo := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = dhi := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = vhi := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = uhi := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_11 : reg n6 a1 = qlo := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_2, show B + 0x21A0 + 0x54 = B + 0x21A0 + BitVec.ofNat 32 0x54 by p2v_addr, w5_54]
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_10 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m6]; exact w5_10
  have w6_14 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m6]; exact w5_14
  have w6_18 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m6]; exact w5_18
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m6]; exact w5_40
  have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m6]; exact w5_54
  have w6_1318 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m6]; exact w5_1318
  have w6_131c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m6]; exact w5_131c
  have w6_1320 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m6]; exact w5_1320
  have w6_1324 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m6]; exact w5_1324
  have b6_220 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m6]; exact b5_220
  have b6_920 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m6]; exact b5_920
  have b6_fa0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m6]; exact b5_fa0
  have b6_1004 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m6]; exact b5_1004
  have a6_180 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m6]; exact a5_180
  have a6_200 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m6]; exact a5_200
  have a6_900 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m6]; exact a5_900
  have a6_980 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m6]; exact a5_980
  have a6_f80 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m6]; exact a5_f80
  have a6_fe4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m6]; exact a5_fe4
  have a6_1338 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m6]; exact a5_1338
  have a6_1358 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m6]; exact a5_1358
  clear a5_1358 a5_1338 a5_fe4 a5_f80 a5_980 a5_900 a5_200 a5_180 w5_1324 b5_1004 b5_fa0 b5_920 b5_220 w5_1320 w5_131c w5_1318 w5_54 w5_40 w5_18 w5_14 w5_10 g5_26 g5_25 g5_24 g5_23 g5_22 g5_20 g5_18 g5_13 g5_10 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 rg5 W5 K5 fr5 s5 d5
  -- 0xE20: sw
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := p2v_sw F E6 s6 p2v_at_e20 (off' := 0xE24) (c := 0x1328)
    (by decide) (by rw [g6_10]; p2v_addr) (by decide) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : P2vCode n7.mem := E6.fr F fr7
  have V7 : P2vSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg7 (8 : Fin 32), g6_8]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by rw [rg7 a0, g6_10]
  have g7_11 : reg n7 a1 = qlo := by rw [rg7 a1, g6_11]
  have g7_13 : reg n7 a3 = rhi := by rw [rg7 a3, g6_13]
  have g7_18 : reg n7 (18 : Fin 32) = qhi := by rw [rg7 (18 : Fin 32), g6_18]
  have g7_20 : reg n7 (20 : Fin 32) = vlo := by rw [rg7 (20 : Fin 32), g6_20]
  have g7_22 : reg n7 (22 : Fin 32) = rlo := by rw [rg7 (22 : Fin 32), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = ulo := by rw [rg7 (23 : Fin 32), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = dhi := by rw [rg7 (24 : Fin 32), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = vhi := by rw [rg7 (25 : Fin 32), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = uhi := by rw [rg7 (26 : Fin 32), g6_26]
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_10 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K7.w32 (by decide) (by decide)).trans w6_10
  have w7_14 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K7.w32 (by decide) (by decide)).trans w6_14
  have w7_18 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K7.w32 (by decide) (by decide)).trans w6_18
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K7.w32 (by decide) (by decide)).trans w6_40
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K7.w32 (by decide) (by decide)).trans w6_54
  have w7_1318 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K7.w32 (by decide) (by decide)).trans w6_1318
  have w7_131c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K7.w32 (by decide) (by decide)).trans w6_131c
  have w7_1320 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := (K7.w32 (by decide) (by decide)).trans w6_1320
  have w7_1324 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := (K7.w32 (by decide) (by decide)).trans w6_1324
  have b7_220 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K7.b8 (by decide) (by decide)).trans b6_220
  have b7_920 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K7.b8 (by decide) (by decide)).trans b6_920
  have b7_fa0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K7.b8 (by decide) (by decide)).trans b6_fa0
  have b7_1004 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K7.b8 (by decide) (by decide)).trans b6_1004
  have w7_1328 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [W7, g6_11]
  have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K7.acc (by decide) (by decide)).trans a6_180
  have a7_200 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K7.acc (by decide) (by decide)).trans a6_200
  have a7_900 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K7.acc (by decide) (by decide)).trans a6_900
  have a7_980 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K7.acc (by decide) (by decide)).trans a6_980
  have a7_f80 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K7.acc (by decide) (by decide)).trans a6_f80
  have a7_fe4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K7.acc (by decide) (by decide)).trans a6_fe4
  have a7_1338 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K7.acc (by decide) (by decide)).trans a6_1338
  have a7_1358 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K7.acc (by decide) (by decide)).trans a6_1358
  clear a6_1358 a6_1338 a6_fe4 a6_f80 a6_980 a6_900 a6_200 a6_180 b6_1004 b6_fa0 b6_920 b6_220 w6_1324 w6_1320 w6_131c w6_1318 w6_54 w6_40 w6_18 w6_14 w6_10 g6_11 g6_26 g6_25 g6_24 g6_23 g6_22 g6_20 g6_18 g6_13 g6_10 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0xE24: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := p2v_sw F E7 s7 p2v_at_e24 (off' := 0xE28) (c := 0x132C)
    (by decide) (by rw [g7_10]; p2v_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, P2vR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : P2vCode n8.mem := E7.fr F fr8
  have V8 : P2vSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg8 (8 : Fin 32), g7_8]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by rw [rg8 a0, g7_10]
  have g8_11 : reg n8 a1 = qlo := by rw [rg8 a1, g7_11]
  have g8_13 : reg n8 a3 = rhi := by rw [rg8 a3, g7_13]
  have g8_18 : reg n8 (18 : Fin 32) = qhi := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_20 : reg n8 (20 : Fin 32) = vlo := by rw [rg8 (20 : Fin 32), g7_20]
  have g8_22 : reg n8 (22 : Fin 32) = rlo := by rw [rg8 (22 : Fin 32), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = ulo := by rw [rg8 (23 : Fin 32), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = dhi := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = vhi := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = uhi := by rw [rg8 (26 : Fin 32), g7_26]
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_10 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K8.w32 (by decide) (by decide)).trans w7_10
  have w8_14 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K8.w32 (by decide) (by decide)).trans w7_14
  have w8_18 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K8.w32 (by decide) (by decide)).trans w7_18
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K8.w32 (by decide) (by decide)).trans w7_40
  have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K8.w32 (by decide) (by decide)).trans w7_54
  have w8_1318 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K8.w32 (by decide) (by decide)).trans w7_1318
  have w8_131c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K8.w32 (by decide) (by decide)).trans w7_131c
  have w8_1320 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := (K8.w32 (by decide) (by decide)).trans w7_1320
  have w8_1324 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := (K8.w32 (by decide) (by decide)).trans w7_1324
  have w8_1328 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := (K8.w32 (by decide) (by decide)).trans w7_1328
  have b8_220 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K8.b8 (by decide) (by decide)).trans b7_220
  have b8_920 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K8.b8 (by decide) (by decide)).trans b7_920
  have b8_fa0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K8.b8 (by decide) (by decide)).trans b7_fa0
  have b8_1004 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K8.b8 (by decide) (by decide)).trans b7_1004
  have w8_132c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [W8, g7_18]
  have a8_180 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K8.acc (by decide) (by decide)).trans a7_180
  have a8_200 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K8.acc (by decide) (by decide)).trans a7_200
  have a8_900 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K8.acc (by decide) (by decide)).trans a7_900
  have a8_980 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K8.acc (by decide) (by decide)).trans a7_980
  have a8_f80 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K8.acc (by decide) (by decide)).trans a7_f80
  have a8_fe4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K8.acc (by decide) (by decide)).trans a7_fe4
  have a8_1338 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K8.acc (by decide) (by decide)).trans a7_1338
  have a8_1358 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K8.acc (by decide) (by decide)).trans a7_1358
  clear a7_1358 a7_1338 a7_fe4 a7_f80 a7_980 a7_900 a7_200 a7_180 w7_1328 b7_1004 b7_fa0 b7_920 b7_220 w7_1324 w7_1320 w7_131c w7_1318 w7_54 w7_40 w7_18 w7_14 w7_10 g7_26 g7_25 g7_24 g7_23 g7_22 g7_20 g7_18 g7_13 g7_11 g7_10 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0xE28: sw
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := p2v_sw F E8 s8 p2v_at_e28 (off' := 0xE2C) (c := 0x1330)
    (by decide) (by rw [g8_10]; p2v_addr) (by decide) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, P2vR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : P2vCode n9.mem := E8.fr F fr9
  have V9 : P2vSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg9 (8 : Fin 32), g8_8]
  have g9_10 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by rw [rg9 a0, g8_10]
  have g9_11 : reg n9 a1 = qlo := by rw [rg9 a1, g8_11]
  have g9_13 : reg n9 a3 = rhi := by rw [rg9 a3, g8_13]
  have g9_18 : reg n9 (18 : Fin 32) = qhi := by rw [rg9 (18 : Fin 32), g8_18]
  have g9_20 : reg n9 (20 : Fin 32) = vlo := by rw [rg9 (20 : Fin 32), g8_20]
  have g9_22 : reg n9 (22 : Fin 32) = rlo := by rw [rg9 (22 : Fin 32), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = ulo := by rw [rg9 (23 : Fin 32), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = dhi := by rw [rg9 (24 : Fin 32), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = vhi := by rw [rg9 (25 : Fin 32), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = uhi := by rw [rg9 (26 : Fin 32), g8_26]
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have w9_10 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K9.w32 (by decide) (by decide)).trans w8_10
  have w9_14 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K9.w32 (by decide) (by decide)).trans w8_14
  have w9_18 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K9.w32 (by decide) (by decide)).trans w8_18
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K9.w32 (by decide) (by decide)).trans w8_40
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K9.w32 (by decide) (by decide)).trans w8_54
  have w9_1318 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K9.w32 (by decide) (by decide)).trans w8_1318
  have w9_131c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K9.w32 (by decide) (by decide)).trans w8_131c
  have w9_1320 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := (K9.w32 (by decide) (by decide)).trans w8_1320
  have w9_1324 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := (K9.w32 (by decide) (by decide)).trans w8_1324
  have w9_1328 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := (K9.w32 (by decide) (by decide)).trans w8_1328
  have w9_132c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := (K9.w32 (by decide) (by decide)).trans w8_132c
  have b9_220 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K9.b8 (by decide) (by decide)).trans b8_220
  have b9_920 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K9.b8 (by decide) (by decide)).trans b8_920
  have b9_fa0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K9.b8 (by decide) (by decide)).trans b8_fa0
  have b9_1004 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K9.b8 (by decide) (by decide)).trans b8_1004
  have w9_1330 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [W9, g8_22]
  have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K9.acc (by decide) (by decide)).trans a8_180
  have a9_200 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K9.acc (by decide) (by decide)).trans a8_200
  have a9_900 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K9.acc (by decide) (by decide)).trans a8_900
  have a9_980 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K9.acc (by decide) (by decide)).trans a8_980
  have a9_f80 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K9.acc (by decide) (by decide)).trans a8_f80
  have a9_fe4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K9.acc (by decide) (by decide)).trans a8_fe4
  have a9_1338 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K9.acc (by decide) (by decide)).trans a8_1338
  have a9_1358 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K9.acc (by decide) (by decide)).trans a8_1358
  clear a8_1358 a8_1338 a8_fe4 a8_f80 a8_980 a8_900 a8_200 a8_180 w8_132c b8_1004 b8_fa0 b8_920 b8_220 w8_1328 w8_1324 w8_1320 w8_131c w8_1318 w8_54 w8_40 w8_18 w8_14 w8_10 g8_26 g8_25 g8_24 g8_23 g8_22 g8_20 g8_18 g8_13 g8_11 g8_10 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0xE2C: sw
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := p2v_sw F E9 s9 p2v_at_e2c (off' := 0xE30) (c := 0x1334)
    (by decide) (by rw [g9_10]; p2v_addr) (by decide) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : P2vCode n10.mem := E9.fr F fr10
  have V10 : P2vSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg10 (8 : Fin 32), g9_8]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by rw [rg10 a0, g9_10]
  have g10_11 : reg n10 a1 = qlo := by rw [rg10 a1, g9_11]
  have g10_13 : reg n10 a3 = rhi := by rw [rg10 a3, g9_13]
  have g10_18 : reg n10 (18 : Fin 32) = qhi := by rw [rg10 (18 : Fin 32), g9_18]
  have g10_20 : reg n10 (20 : Fin 32) = vlo := by rw [rg10 (20 : Fin 32), g9_20]
  have g10_22 : reg n10 (22 : Fin 32) = rlo := by rw [rg10 (22 : Fin 32), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = ulo := by rw [rg10 (23 : Fin 32), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = dhi := by rw [rg10 (24 : Fin 32), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = vhi := by rw [rg10 (25 : Fin 32), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = uhi := by rw [rg10 (26 : Fin 32), g9_26]
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_10 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K10.w32 (by decide) (by decide)).trans w9_10
  have w10_14 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K10.w32 (by decide) (by decide)).trans w9_14
  have w10_18 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K10.w32 (by decide) (by decide)).trans w9_18
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K10.w32 (by decide) (by decide)).trans w9_40
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K10.w32 (by decide) (by decide)).trans w9_54
  have w10_1318 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K10.w32 (by decide) (by decide)).trans w9_1318
  have w10_131c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K10.w32 (by decide) (by decide)).trans w9_131c
  have w10_1320 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := (K10.w32 (by decide) (by decide)).trans w9_1320
  have w10_1324 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := (K10.w32 (by decide) (by decide)).trans w9_1324
  have w10_1328 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := (K10.w32 (by decide) (by decide)).trans w9_1328
  have w10_132c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := (K10.w32 (by decide) (by decide)).trans w9_132c
  have w10_1330 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := (K10.w32 (by decide) (by decide)).trans w9_1330
  have b10_220 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K10.b8 (by decide) (by decide)).trans b9_220
  have b10_920 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K10.b8 (by decide) (by decide)).trans b9_920
  have b10_fa0 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K10.b8 (by decide) (by decide)).trans b9_fa0
  have b10_1004 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K10.b8 (by decide) (by decide)).trans b9_1004
  have w10_1334 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [W10, g9_13]
  have a10_180 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K10.acc (by decide) (by decide)).trans a9_180
  have a10_200 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K10.acc (by decide) (by decide)).trans a9_200
  have a10_900 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K10.acc (by decide) (by decide)).trans a9_900
  have a10_980 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K10.acc (by decide) (by decide)).trans a9_980
  have a10_f80 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K10.acc (by decide) (by decide)).trans a9_f80
  have a10_fe4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K10.acc (by decide) (by decide)).trans a9_fe4
  have a10_1338 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K10.acc (by decide) (by decide)).trans a9_1338
  have a10_1358 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K10.acc (by decide) (by decide)).trans a9_1358
  clear a9_1358 a9_1338 a9_fe4 a9_f80 a9_980 a9_900 a9_200 a9_180 w9_1330 b9_1004 b9_fa0 b9_920 b9_220 w9_132c w9_1328 w9_1324 w9_1320 w9_131c w9_1318 w9_54 w9_40 w9_18 w9_14 w9_10 g9_26 g9_25 g9_24 g9_23 g9_22 g9_20 g9_18 g9_13 g9_11 g9_10 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  -- 0xE30
  obtain ⟨n11, c11, u11⟩ := s10.block p2vZBe30 E10.self p2vZBe30_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem P2V n11 0xE50 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock p2vZBe30 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
  have fr11 : ∀ x, P2vR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : P2vCode n11.mem := E10.fr F fr11
  have V11 : P2vSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by
    rw [rb11, runBlock_reg _ _ _ sp s10.zero (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (3 : Fin 32) s10.zero (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (4 : Fin 32) s10.zero (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb11, runBlock_reg _ _ _ (8 : Fin 32) s10.zero (by decide), g10_8]
  have g11_18 : reg n11 (18 : Fin 32) = qhi := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_20 : reg n11 (20 : Fin 32) = vlo := by
    rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
  have g11_22 : reg n11 (22 : Fin 32) = rlo := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = ulo := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = dhi := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = vhi := by
    rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = uhi := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_10 : reg n11 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vZBe30, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_10, g10_11, g10_13, g10_18, g10_20, g10_22, g10_23, g10_24, g10_25, g10_26, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g11_11 : reg n11 a1 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vZBe30, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_10, g10_11, g10_13, g10_18, g10_20, g10_22, g10_23, g10_24, g10_25, g10_26, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g11_12 : reg n11 a2 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vZBe30, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_10, g10_11, g10_13, g10_18, g10_20, g10_22, g10_23, g10_24, g10_25, g10_26, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g11_13 : reg n11 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1318 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vZBe30, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_10, g10_11, g10_13, g10_18, g10_20, g10_22, g10_23, g10_24, g10_25, g10_26, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_10 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m11]; exact w10_10
  have w11_14 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m11]; exact w10_14
  have w11_18 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m11]; exact w10_18
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m11]; exact w10_40
  have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m11]; exact w10_54
  have w11_1318 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m11]; exact w10_1318
  have w11_131c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m11]; exact w10_131c
  have w11_1320 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m11]; exact w10_1320
  have w11_1324 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m11]; exact w10_1324
  have w11_1328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [m11]; exact w10_1328
  have w11_132c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [m11]; exact w10_132c
  have w11_1330 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [m11]; exact w10_1330
  have w11_1334 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [m11]; exact w10_1334
  have b11_220 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m11]; exact b10_220
  have b11_920 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m11]; exact b10_920
  have b11_fa0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m11]; exact b10_fa0
  have b11_1004 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m11]; exact b10_1004
  have a11_180 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m11]; exact a10_180
  have a11_200 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m11]; exact a10_200
  have a11_900 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m11]; exact a10_900
  have a11_980 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m11]; exact a10_980
  have a11_f80 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m11]; exact a10_f80
  have a11_fe4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m11]; exact a10_fe4
  have a11_1338 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m11]; exact a10_1338
  have a11_1358 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m11]; exact a10_1358
  clear a10_1358 a10_1338 a10_fe4 a10_f80 a10_980 a10_900 a10_200 a10_180 w10_1334 b10_1004 b10_fa0 b10_920 b10_220 w10_1330 w10_132c w10_1328 w10_1324 w10_1320 w10_131c w10_1318 w10_54 w10_40 w10_18 w10_14 w10_10 g10_26 g10_25 g10_24 g10_23 g10_22 g10_20 g10_18 g10_13 g10_11 g10_10 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0xE50: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self p2v_at_e50 (off' := 0xE52) (by decide)
    (by rw [g11_2, show B + 0x21A0 + 0x14 = B + 0x21A0 + BitVec.ofNat 32 0x14 by p2v_addr]; exact p2v_al F (by decide) (by decide))
  have s12 : St n12.mem P2V n12 0xE52 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, P2vR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, P2vR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : P2vCode n12.mem := E11.fr F fr12
  have V12 : P2vSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_10]
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_11]
  have g12_12 : reg n12 a2 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_12]
  have g12_13 : reg n12 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1318 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_13]
  have g12_18 : reg n12 (18 : Fin 32) = qhi := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_20 : reg n12 (20 : Fin 32) = vlo := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
  have g12_22 : reg n12 (22 : Fin 32) = rlo := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = ulo := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = dhi := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = vhi := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = uhi := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_9 : reg n12 (9 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x14 = B + 0x21A0 + BitVec.ofNat 32 0x14 by p2v_addr, w11_14]
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_10 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m12]; exact w11_10
  have w12_14 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m12]; exact w11_14
  have w12_18 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m12]; exact w11_18
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m12]; exact w11_40
  have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m12]; exact w11_54
  have w12_1318 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m12]; exact w11_1318
  have w12_131c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m12]; exact w11_131c
  have w12_1320 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m12]; exact w11_1320
  have w12_1324 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m12]; exact w11_1324
  have w12_1328 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [m12]; exact w11_1328
  have w12_132c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [m12]; exact w11_132c
  have w12_1330 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [m12]; exact w11_1330
  have w12_1334 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [m12]; exact w11_1334
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
  clear a11_1358 a11_1338 a11_fe4 a11_f80 a11_980 a11_900 a11_200 a11_180 b11_1004 b11_fa0 b11_920 b11_220 w11_1334 w11_1330 w11_132c w11_1328 w11_1324 w11_1320 w11_131c w11_1318 w11_54 w11_40 w11_18 w11_14 w11_10 g11_13 g11_12 g11_11 g11_10 g11_26 g11_25 g11_24 g11_23 g11_22 g11_20 g11_18 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0xE52
  obtain ⟨n13, c13, u13⟩ := s12.block p2vZBe52 E12.self p2vZBe52_end
    ⟨trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem P2V n13 0xE54 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock p2vZBe52 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  have fr13 : ∀ x, P2vR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, P2vR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : P2vCode n13.mem := E12.fr F fr13
  have V13 : P2vSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by
    rw [rb13, runBlock_reg _ _ _ sp s12.zero (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb13, runBlock_reg _ _ _ (3 : Fin 32) s12.zero (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb13, runBlock_reg _ _ _ (4 : Fin 32) s12.zero (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb13, runBlock_reg _ _ _ a0 s12.zero (by decide), g12_10]
  have g13_11 : reg n13 a1 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb13, runBlock_reg _ _ _ a1 s12.zero (by decide), g12_11]
  have g13_12 : reg n13 a2 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb13, runBlock_reg _ _ _ a2 s12.zero (by decide), g12_12]
  have g13_13 : reg n13 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1318 := by
    rw [rb13, runBlock_reg _ _ _ a3 s12.zero (by decide), g12_13]
  have g13_18 : reg n13 (18 : Fin 32) = qhi := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_20 : reg n13 (20 : Fin 32) = vlo := by
    rw [rb13, runBlock_reg _ _ _ (20 : Fin 32) s12.zero (by decide), g12_20]
  have g13_22 : reg n13 (22 : Fin 32) = rlo := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = ulo := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = dhi := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = vhi := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = uhi := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_14 : reg n13 a4 = BitVec.ofNat 32 ns := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vZBe52, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_10, g12_11, g12_12, g12_13, g12_18, g12_20, g12_22, g12_23, g12_24, g12_25, g12_26, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk13 : P2vKeepL B n0.mem n13.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_10 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m13]; exact w12_10
  have w13_14 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m13]; exact w12_14
  have w13_18 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m13]; exact w12_18
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m13]; exact w12_40
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m13]; exact w12_54
  have w13_1318 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m13]; exact w12_1318
  have w13_131c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m13]; exact w12_131c
  have w13_1320 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m13]; exact w12_1320
  have w13_1324 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m13]; exact w12_1324
  have w13_1328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [m13]; exact w12_1328
  have w13_132c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [m13]; exact w12_132c
  have w13_1330 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [m13]; exact w12_1330
  have w13_1334 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [m13]; exact w12_1334
  have b13_220 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m13]; exact b12_220
  have b13_920 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m13]; exact b12_920
  have b13_fa0 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m13]; exact b12_fa0
  have b13_1004 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m13]; exact b12_1004
  have a13_180 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m13]; exact a12_180
  have a13_200 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m13]; exact a12_200
  have a13_900 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m13]; exact a12_900
  have a13_980 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m13]; exact a12_980
  have a13_f80 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m13]; exact a12_f80
  have a13_fe4 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m13]; exact a12_fe4
  have a13_1338 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m13]; exact a12_1338
  have a13_1358 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m13]; exact a12_1358
  clear a12_1358 a12_1338 a12_fe4 a12_f80 a12_980 a12_900 a12_200 a12_180 b12_1004 b12_fa0 b12_920 b12_220 w12_1334 w12_1330 w12_132c w12_1328 w12_1324 w12_1320 w12_131c w12_1318 w12_54 w12_40 w12_18 w12_14 w12_10 g12_9 g12_26 g12_25 g12_24 g12_23 g12_22 g12_20 g12_18 g12_13 g12_12 g12_11 g12_10 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0xE54: p2v_ufg8F
  obtain ⟨n14, c14, s14, sp14, rk14, R1_14, R2_14, K14, fr14⟩ := p2v_ufg8F (co := 0xC80) (ca := 0xF80) (cb := 0x900) (ct := 0x1318) (s := ns)
    F E13 (UC0.p2v F fR13) s13 p2v_at_e54 p2v_at_e58 (by decide) (by decide) g13_2
    g13_10 g13_11 g13_12 g13_13 g13_14 hns1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) 
    (by rw [show 0xF80 + 0x20 = 0xFA0 from rfl, b13_fa0]; exact hfs)
    (by rw [show 0x900 + 0x20 = 0x920 from rfl, b13_920]; exact hgs)
  obtain ⟨σ14a, A14a, hσ0_14, e0_14, bb0_14, vv0_14⟩ := R1_14
  simp only [p2vI, p2vM, show 0xF80 + 0x20 = 0xFA0 from rfl, show 0x900 + 0x20 = 0x920 from rfl,
    show 0x1318 + 0x0 = 0x1318 from rfl, show 0x1318 + 0x8 = 0x1320 from rfl] at e0_14
  rw [b13_fa0, a13_f80, b13_920, a13_900,
    acc2_frame w13_1318 w13_131c, acc2_frame w13_1320 w13_1324] at e0_14
  obtain ⟨σ14b, A14b, hσ1_14, e1_14, bb1_14, vv1_14⟩ := R2_14
  simp only [p2vI, p2vM, show 0xF80 + 0x20 = 0xFA0 from rfl, show 0x900 + 0x20 = 0x920 from rfl,
    show 0x1318 + 0x10 = 0x1328 from rfl, show 0x1318 + 0x18 = 0x1330 from rfl] at e1_14
  rw [b13_fa0, a13_f80, b13_920, a13_900,
    acc2_frame w13_1328 w13_132c, acc2_frame w13_1330 w13_1334] at e1_14
  have t14 : Steps n0 n14 := t13.trans c14
  have fR14 : ∀ x, P2vR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : P2vCode n14.mem := E13.fr F fr14
  have V14 : P2vSaves B n14.mem v := V13.keepL K14 (by decide)
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk14 (3 : Fin 32) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk14 (4 : Fin 32) (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk14 (8 : Fin 32) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = BitVec.ofNat 32 ns := by rw [rk14 (9 : Fin 32) (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = qhi := by rw [rk14 (18 : Fin 32) (by decide), g13_18]
  have g14_20 : reg n14 (20 : Fin 32) = vlo := by rw [rk14 (20 : Fin 32) (by decide), g13_20]
  have g14_22 : reg n14 (22 : Fin 32) = rlo := by rw [rk14 (22 : Fin 32) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = ulo := by rw [rk14 (23 : Fin 32) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = dhi := by rw [rk14 (24 : Fin 32) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = vhi := by rw [rk14 (25 : Fin 32) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = uhi := by rw [rk14 (26 : Fin 32) (by decide), g13_26]
  have g14_2 : reg n14 sp = B + 0x21A0 := sp14
  have keep_kk14 : P2vKeepL B n0.mem n14.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45)] := keep_kk13.trans K14
  clear keep_kk13
  have w14_10 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K14.w32 (by decide) (by decide)).trans w13_10
  have w14_14 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K14.w32 (by decide) (by decide)).trans w13_14
  have w14_18 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K14.w32 (by decide) (by decide)).trans w13_18
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K14.w32 (by decide) (by decide)).trans w13_40
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K14.w32 (by decide) (by decide)).trans w13_54
  have w14_1318 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K14.w32 (by decide) (by decide)).trans w13_1318
  have w14_131c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K14.w32 (by decide) (by decide)).trans w13_131c
  have w14_1320 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := (K14.w32 (by decide) (by decide)).trans w13_1320
  have w14_1324 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := (K14.w32 (by decide) (by decide)).trans w13_1324
  have w14_1328 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := (K14.w32 (by decide) (by decide)).trans w13_1328
  have w14_132c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := (K14.w32 (by decide) (by decide)).trans w13_132c
  have w14_1330 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := (K14.w32 (by decide) (by decide)).trans w13_1330
  have w14_1334 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := (K14.w32 (by decide) (by decide)).trans w13_1334
  have b14_220 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K14.b8 (by decide) (by decide)).trans b13_220
  have b14_920 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K14.b8 (by decide) (by decide)).trans b13_920
  have b14_fa0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K14.b8 (by decide) (by decide)).trans b13_fa0
  have b14_1004 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K14.b8 (by decide) (by decide)).trans b13_1004
  have a14_180 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K14.acc (by decide) (by decide)).trans a13_180
  have a14_200 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K14.acc (by decide) (by decide)).trans a13_200
  have a14_900 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K14.acc (by decide) (by decide)).trans a13_900
  have a14_980 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K14.acc (by decide) (by decide)).trans a13_980
  have a14_f80 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K14.acc (by decide) (by decide)).trans a13_f80
  have a14_fe4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K14.acc (by decide) (by decide)).trans a13_fe4
  have a14_1338 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K14.acc (by decide) (by decide)).trans a13_1338
  have a14_1358 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K14.acc (by decide) (by decide)).trans a13_1358
  have a14_c80 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A14a / 2 ^ ns % 2 ^ 256 := vv0_14
  have a14_ca4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A14b / 2 ^ ns % 2 ^ 256 := vv1_14
  have b14_ca0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ14a := byte_of_toNat bb0_14
  have b14_cc4 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ14b := byte_of_toNat bb1_14
  clear a13_1358 a13_1338 a13_fe4 a13_f80 a13_980 a13_900 a13_200 a13_180 b13_1004 b13_fa0 b13_920 b13_220 w13_1334 w13_1330 w13_132c w13_1328 w13_1324 w13_1320 w13_131c w13_1318 w13_54 w13_40 w13_18 w13_14 w13_10 g13_14 g13_26 g13_25 g13_24 g13_23 g13_22 g13_20 g13_18 g13_13 g13_12 g13_11 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0xE5C
  obtain ⟨n15, c15, u15⟩ := s14.block p2vZBe5c E14.self p2vZBe5c_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem P2V n15 0xE70 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock p2vZBe5c (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
  have fr15 : ∀ x, P2vR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, P2vR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : P2vCode n15.mem := E14.fr F fr15
  have V15 : P2vSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by
    rw [rb15, runBlock_reg _ _ _ sp s14.zero (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (3 : Fin 32) s14.zero (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (4 : Fin 32) s14.zero (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb15, runBlock_reg _ _ _ (8 : Fin 32) s14.zero (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb15, runBlock_reg _ _ _ (9 : Fin 32) s14.zero (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = qhi := by
    rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
  have g15_20 : reg n15 (20 : Fin 32) = vlo := by
    rw [rb15, runBlock_reg _ _ _ (20 : Fin 32) s14.zero (by decide), g14_20]
  have g15_22 : reg n15 (22 : Fin 32) = rlo := by
    rw [rb15, runBlock_reg _ _ _ (22 : Fin 32) s14.zero (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = ulo := by
    rw [rb15, runBlock_reg _ _ _ (23 : Fin 32) s14.zero (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = dhi := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = vhi := by
    rw [rb15, runBlock_reg _ _ _ (25 : Fin 32) s14.zero (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = uhi := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vZBe5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_20, g14_22, g14_23, g14_24, g14_25, g14_26, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g15_11 : reg n15 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vZBe5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_20, g14_22, g14_23, g14_24, g14_25, g14_26, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g15_12 : reg n15 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vZBe5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_20, g14_22, g14_23, g14_24, g14_25, g14_26, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_10 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m15]; exact w14_10
  have w15_14 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m15]; exact w14_14
  have w15_18 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m15]; exact w14_18
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m15]; exact w14_40
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m15]; exact w14_54
  have w15_1318 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m15]; exact w14_1318
  have w15_131c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m15]; exact w14_131c
  have w15_1320 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m15]; exact w14_1320
  have w15_1324 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m15]; exact w14_1324
  have w15_1328 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [m15]; exact w14_1328
  have w15_132c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [m15]; exact w14_132c
  have w15_1330 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [m15]; exact w14_1330
  have w15_1334 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [m15]; exact w14_1334
  have b15_220 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m15]; exact b14_220
  have b15_920 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m15]; exact b14_920
  have b15_ca0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ14a := by rw [m15]; exact b14_ca0
  have b15_cc4 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ14b := by rw [m15]; exact b14_cc4
  have b15_fa0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m15]; exact b14_fa0
  have b15_1004 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m15]; exact b14_1004
  have a15_180 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m15]; exact a14_180
  have a15_200 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m15]; exact a14_200
  have a15_900 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m15]; exact a14_900
  have a15_980 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m15]; exact a14_980
  have a15_c80 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A14a / 2 ^ ns % 2 ^ 256 := by rw [m15]; exact a14_c80
  have a15_ca4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A14b / 2 ^ ns % 2 ^ 256 := by rw [m15]; exact a14_ca4
  have a15_f80 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m15]; exact a14_f80
  have a15_fe4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m15]; exact a14_fe4
  have a15_1338 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m15]; exact a14_1338
  have a15_1358 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m15]; exact a14_1358
  clear b14_cc4 b14_ca0 a14_ca4 a14_c80 a14_1358 a14_1338 a14_fe4 a14_f80 a14_980 a14_900 a14_200 a14_180 b14_1004 b14_fa0 b14_920 b14_220 w14_1334 w14_1330 w14_132c w14_1328 w14_1324 w14_1320 w14_131c w14_1318 w14_54 w14_40 w14_18 w14_14 w14_10 g14_2 g14_26 g14_25 g14_24 g14_23 g14_22 g14_20 g14_18 g14_9 g14_8 g14_4 g14_3 V14 E14 fR14 t14 vv1_14 bb1_14 vv0_14 bb0_14 fr14 K14 rk14 sp14 s14 c14
  -- 0xE70: memcpy
  obtain ⟨n16, P16, K16, X16⟩ := p2v_mc (c := 0xF80) (d := 0xC80) (N := 0x24) F E15 s15 p2v_at_e70 p2v_at_e74
    (by decide) (by decide) g15_2 g15_10 g15_11 g15_12
    (by decide) (by decide) (by decide)
  have s16 := P16.st
  have fr16 := P16.fr
  have t16 : Steps n0 n16 := t15.trans P16.steps
  have fR16 : ∀ x, P2vR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : P2vCode n16.mem := E15.fr F fr16
  have V16 : P2vSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [P16.regs sp (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P16.regs (3 : Fin 32) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P16.regs (4 : Fin 32) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P16.regs (8 : Fin 32) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = BitVec.ofNat 32 ns := by rw [P16.regs (9 : Fin 32) (by decide), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = qhi := by rw [P16.regs (18 : Fin 32) (by decide), g15_18]
  have g16_20 : reg n16 (20 : Fin 32) = vlo := by rw [P16.regs (20 : Fin 32) (by decide), g15_20]
  have g16_22 : reg n16 (22 : Fin 32) = rlo := by rw [P16.regs (22 : Fin 32) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = ulo := by rw [P16.regs (23 : Fin 32) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = dhi := by rw [P16.regs (24 : Fin 32) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = vhi := by rw [P16.regs (25 : Fin 32) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = uhi := by rw [P16.regs (26 : Fin 32) (by decide), g15_26]
  have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_10 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K16.w32 (by decide) (by decide)).trans w15_10
  have w16_14 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K16.w32 (by decide) (by decide)).trans w15_14
  have w16_18 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K16.w32 (by decide) (by decide)).trans w15_18
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K16.w32 (by decide) (by decide)).trans w15_40
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K16.w32 (by decide) (by decide)).trans w15_54
  have w16_1318 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K16.w32 (by decide) (by decide)).trans w15_1318
  have w16_131c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K16.w32 (by decide) (by decide)).trans w15_131c
  have w16_1320 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := (K16.w32 (by decide) (by decide)).trans w15_1320
  have w16_1324 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := (K16.w32 (by decide) (by decide)).trans w15_1324
  have w16_1328 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := (K16.w32 (by decide) (by decide)).trans w15_1328
  have w16_132c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := (K16.w32 (by decide) (by decide)).trans w15_132c
  have w16_1330 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := (K16.w32 (by decide) (by decide)).trans w15_1330
  have w16_1334 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := (K16.w32 (by decide) (by decide)).trans w15_1334
  have b16_220 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K16.b8 (by decide) (by decide)).trans b15_220
  have b16_920 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K16.b8 (by decide) (by decide)).trans b15_920
  have b16_ca0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ14a := (K16.b8 (by decide) (by decide)).trans b15_ca0
  have b16_cc4 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ14b := (K16.b8 (by decide) (by decide)).trans b15_cc4
  have b16_1004 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K16.b8 (by decide) (by decide)).trans b15_1004
  have b16_fa0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := by rw [show 0xFA0 = 0xF80 + 0x20 from rfl, X16 0x20 (by decide)]; exact b15_ca0
  have a16_180 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K16.acc (by decide) (by decide)).trans a15_180
  have a16_200 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K16.acc (by decide) (by decide)).trans a15_200
  have a16_900 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K16.acc (by decide) (by decide)).trans a15_900
  have a16_980 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K16.acc (by decide) (by decide)).trans a15_980
  have a16_c80 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A14a / 2 ^ ns % 2 ^ 256 := (K16.acc (by decide) (by decide)).trans a15_c80
  have a16_ca4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A14b / 2 ^ ns % 2 ^ 256 := (K16.acc (by decide) (by decide)).trans a15_ca4
  have a16_fe4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K16.acc (by decide) (by decide)).trans a15_fe4
  have a16_1338 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K16.acc (by decide) (by decide)).trans a15_1338
  have a16_1358 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K16.acc (by decide) (by decide)).trans a15_1358
  have a16_f80 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := (accV_S 8 fun q hq => by
    rw [show 0xF80 + q = 0xF80 + (0x0 + q) by omega, X16 (0x0 + q) (by omega),
      show 0xC80 + (0x0 + q) = 0xC80 + q by omega]).trans a15_c80
  clear a15_1358 a15_1338 a15_fe4 a15_f80 a15_ca4 a15_c80 a15_980 a15_900 a15_200 a15_180 b15_1004 b15_fa0 b15_cc4 b15_ca0 b15_920 b15_220 w15_1334 w15_1330 w15_132c w15_1328 w15_1324 w15_1320 w15_131c w15_1318 w15_54 w15_40 w15_18 w15_14 w15_10 g15_12 g15_11 g15_10 g15_26 g15_25 g15_24 g15_23 g15_22 g15_20 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  -- 0xE78
  obtain ⟨n17, c17, u17⟩ := s16.block p2vZBe78 E16.self p2vZBe78_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem P2V n17 0xE8C (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock p2vZBe78 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
  have fr17 : ∀ x, P2vR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans c17
  have fR17 : ∀ x, P2vR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : P2vCode n17.mem := E16.fr F fr17
  have V17 : P2vSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by
    rw [rb17, runBlock_reg _ _ _ sp s16.zero (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (3 : Fin 32) s16.zero (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (4 : Fin 32) s16.zero (by decide), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = qhi := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_20 : reg n17 (20 : Fin 32) = vlo := by
    rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
  have g17_22 : reg n17 (22 : Fin 32) = rlo := by
    rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = ulo := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = dhi := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = vhi := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = uhi := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vZBe78, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_20, g16_22, g16_23, g16_24, g16_25, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_11 : reg n17 a1 = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vZBe78, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_20, g16_22, g16_23, g16_24, g16_25, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vZBe78, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_20, g16_22, g16_23, g16_24, g16_25, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_10 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m17]; exact w16_10
  have w17_14 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m17]; exact w16_14
  have w17_18 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m17]; exact w16_18
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m17]; exact w16_40
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m17]; exact w16_54
  have w17_1318 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m17]; exact w16_1318
  have w17_131c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m17]; exact w16_131c
  have w17_1320 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m17]; exact w16_1320
  have w17_1324 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m17]; exact w16_1324
  have w17_1328 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [m17]; exact w16_1328
  have w17_132c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [m17]; exact w16_132c
  have w17_1330 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [m17]; exact w16_1330
  have w17_1334 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [m17]; exact w16_1334
  have b17_220 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m17]; exact b16_220
  have b17_920 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m17]; exact b16_920
  have b17_ca0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ14a := by rw [m17]; exact b16_ca0
  have b17_cc4 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ14b := by rw [m17]; exact b16_cc4
  have b17_fa0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := by rw [m17]; exact b16_fa0
  have b17_1004 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m17]; exact b16_1004
  have a17_180 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m17]; exact a16_180
  have a17_200 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m17]; exact a16_200
  have a17_900 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m17]; exact a16_900
  have a17_980 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m17]; exact a16_980
  have a17_c80 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A14a / 2 ^ ns % 2 ^ 256 := by rw [m17]; exact a16_c80
  have a17_ca4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A14b / 2 ^ ns % 2 ^ 256 := by rw [m17]; exact a16_ca4
  have a17_f80 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := by rw [m17]; exact a16_f80
  have a17_fe4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m17]; exact a16_fe4
  have a17_1338 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m17]; exact a16_1338
  have a17_1358 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m17]; exact a16_1358
  clear a16_f80 a16_1358 a16_1338 a16_fe4 a16_ca4 a16_c80 a16_980 a16_900 a16_200 a16_180 b16_fa0 b16_1004 b16_cc4 b16_ca0 b16_920 b16_220 w16_1334 w16_1330 w16_132c w16_1328 w16_1324 w16_1320 w16_131c w16_1318 w16_54 w16_40 w16_18 w16_14 w16_10 g16_26 g16_25 g16_24 g16_23 g16_22 g16_20 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 s16 X16 K16 P16
  -- 0xE8C: memcpy
  obtain ⟨n18, P18, K18, X18⟩ := p2v_mc (c := 0x900) (d := 0xCA4) (N := 0x24) F E17 s17 p2v_at_e8c p2v_at_e90
    (by decide) (by decide) g17_2 g17_10 g17_11 g17_12
    (by decide) (by decide) (by decide)
  have s18 := P18.st
  have fr18 := P18.fr
  have t18 : Steps n0 n18 := t17.trans P18.steps
  have fR18 : ∀ x, P2vR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : P2vCode n18.mem := E17.fr F fr18
  have V18 : P2vSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [P18.regs sp (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P18.regs (3 : Fin 32) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P18.regs (4 : Fin 32) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P18.regs (8 : Fin 32) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = BitVec.ofNat 32 ns := by rw [P18.regs (9 : Fin 32) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = qhi := by rw [P18.regs (18 : Fin 32) (by decide), g17_18]
  have g18_20 : reg n18 (20 : Fin 32) = vlo := by rw [P18.regs (20 : Fin 32) (by decide), g17_20]
  have g18_22 : reg n18 (22 : Fin 32) = rlo := by rw [P18.regs (22 : Fin 32) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = ulo := by rw [P18.regs (23 : Fin 32) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = dhi := by rw [P18.regs (24 : Fin 32) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = vhi := by rw [P18.regs (25 : Fin 32) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = uhi := by rw [P18.regs (26 : Fin 32) (by decide), g17_26]
  have keep_kk18 : P2vKeepL B n0.mem n18.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24), (0x900, 0x24)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_10 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K18.w32 (by decide) (by decide)).trans w17_10
  have w18_14 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K18.w32 (by decide) (by decide)).trans w17_14
  have w18_18 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K18.w32 (by decide) (by decide)).trans w17_18
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K18.w32 (by decide) (by decide)).trans w17_40
  have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K18.w32 (by decide) (by decide)).trans w17_54
  have w18_1318 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K18.w32 (by decide) (by decide)).trans w17_1318
  have w18_131c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K18.w32 (by decide) (by decide)).trans w17_131c
  have w18_1320 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := (K18.w32 (by decide) (by decide)).trans w17_1320
  have w18_1324 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := (K18.w32 (by decide) (by decide)).trans w17_1324
  have w18_1328 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := (K18.w32 (by decide) (by decide)).trans w17_1328
  have w18_132c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := (K18.w32 (by decide) (by decide)).trans w17_132c
  have w18_1330 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := (K18.w32 (by decide) (by decide)).trans w17_1330
  have w18_1334 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := (K18.w32 (by decide) (by decide)).trans w17_1334
  have b18_220 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K18.b8 (by decide) (by decide)).trans b17_220
  have b18_ca0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ14a := (K18.b8 (by decide) (by decide)).trans b17_ca0
  have b18_cc4 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ14b := (K18.b8 (by decide) (by decide)).trans b17_cc4
  have b18_fa0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := (K18.b8 (by decide) (by decide)).trans b17_fa0
  have b18_1004 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K18.b8 (by decide) (by decide)).trans b17_1004
  have b18_920 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ14b := by rw [show 0x920 = 0x900 + 0x20 from rfl, X18 0x20 (by decide)]; exact b17_cc4
  have a18_180 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K18.acc (by decide) (by decide)).trans a17_180
  have a18_200 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K18.acc (by decide) (by decide)).trans a17_200
  have a18_980 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K18.acc (by decide) (by decide)).trans a17_980
  have a18_c80 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A14a / 2 ^ ns % 2 ^ 256 := (K18.acc (by decide) (by decide)).trans a17_c80
  have a18_ca4 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A14b / 2 ^ ns % 2 ^ 256 := (K18.acc (by decide) (by decide)).trans a17_ca4
  have a18_f80 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := (K18.acc (by decide) (by decide)).trans a17_f80
  have a18_fe4 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K18.acc (by decide) (by decide)).trans a17_fe4
  have a18_1338 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K18.acc (by decide) (by decide)).trans a17_1338
  have a18_1358 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K18.acc (by decide) (by decide)).trans a17_1358
  have a18_900 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A14b / 2 ^ ns % 2 ^ 256 := (accV_S 8 fun q hq => by
    rw [show 0x900 + q = 0x900 + (0x0 + q) by omega, X18 (0x0 + q) (by omega),
      show 0xCA4 + (0x0 + q) = 0xCA4 + q by omega]).trans a17_ca4
  clear a17_1358 a17_1338 a17_fe4 a17_f80 a17_ca4 a17_c80 a17_980 a17_900 a17_200 a17_180 b17_1004 b17_fa0 b17_cc4 b17_ca0 b17_920 b17_220 w17_1334 w17_1330 w17_132c w17_1328 w17_1324 w17_1320 w17_131c w17_1318 w17_54 w17_40 w17_18 w17_14 w17_10 g17_12 g17_11 g17_10 g17_26 g17_25 g17_24 g17_23 g17_22 g17_20 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0xE94
  obtain ⟨n19, c19, u19⟩ := s18.block p2vZBe94 E18.self p2vZBe94_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem P2V n19 0xEBC (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock p2vZBe94 (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
  have fr19 : ∀ x, P2vR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, P2vR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : P2vCode n19.mem := E18.fr F fr19
  have V19 : P2vSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by
    rw [rb19, runBlock_reg _ _ _ sp s18.zero (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (3 : Fin 32) s18.zero (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (4 : Fin 32) s18.zero (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb19, runBlock_reg _ _ _ (9 : Fin 32) s18.zero (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = qhi := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_20 : reg n19 (20 : Fin 32) = vlo := by
    rw [rb19, runBlock_reg _ _ _ (20 : Fin 32) s18.zero (by decide), g18_20]
  have g19_22 : reg n19 (22 : Fin 32) = rlo := by
    rw [rb19, runBlock_reg _ _ _ (22 : Fin 32) s18.zero (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = ulo := by
    rw [rb19, runBlock_reg _ _ _ (23 : Fin 32) s18.zero (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = dhi := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = vhi := by
    rw [rb19, runBlock_reg _ _ _ (25 : Fin 32) s18.zero (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = uhi := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vZBe94, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_20, g18_22, g18_23, g18_24, g18_25, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vZBe94, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_20, g18_22, g18_23, g18_24, g18_25, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_12 : reg n19 a2 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vZBe94, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_20, g18_22, g18_23, g18_24, g18_25, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_13 : reg n19 a3 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vZBe94, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_20, g18_22, g18_23, g18_24, g18_25, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_14 : reg n19 a4 = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vZBe94, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_20, g18_22, g18_23, g18_24, g18_25, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_15 : reg n19 a5 = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vZBe94, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_20, g18_22, g18_23, g18_24, g18_25, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_16 : reg n19 a6 = B + 0x21A0 + BitVec.ofNat 32 0x1318 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vZBe94, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_20, g18_22, g18_23, g18_24, g18_25, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_17 : reg n19 a7 = BitVec.ofNat 32 ns := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vZBe94, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_20, g18_22, g18_23, g18_24, g18_25, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk19 : P2vKeepL B n0.mem n19.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24), (0x900, 0x24)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_10 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m19]; exact w18_10
  have w19_14 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m19]; exact w18_14
  have w19_18 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m19]; exact w18_18
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m19]; exact w18_40
  have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m19]; exact w18_54
  have w19_1318 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m19]; exact w18_1318
  have w19_131c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m19]; exact w18_131c
  have w19_1320 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m19]; exact w18_1320
  have w19_1324 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m19]; exact w18_1324
  have w19_1328 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [m19]; exact w18_1328
  have w19_132c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [m19]; exact w18_132c
  have w19_1330 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [m19]; exact w18_1330
  have w19_1334 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [m19]; exact w18_1334
  have b19_220 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m19]; exact b18_220
  have b19_920 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ14b := by rw [m19]; exact b18_920
  have b19_ca0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 σ14a := by rw [m19]; exact b18_ca0
  have b19_cc4 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 σ14b := by rw [m19]; exact b18_cc4
  have b19_fa0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := by rw [m19]; exact b18_fa0
  have b19_1004 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m19]; exact b18_1004
  have a19_180 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m19]; exact a18_180
  have a19_200 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m19]; exact a18_200
  have a19_900 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A14b / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_900
  have a19_980 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m19]; exact a18_980
  have a19_c80 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = A14a / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_c80
  have a19_ca4 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = A14b / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_ca4
  have a19_f80 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_f80
  have a19_fe4 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m19]; exact a18_fe4
  have a19_1338 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m19]; exact a18_1338
  have a19_1358 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m19]; exact a18_1358
  clear a18_900 a18_1358 a18_1338 a18_fe4 a18_f80 a18_ca4 a18_c80 a18_980 a18_200 a18_180 b18_920 b18_1004 b18_fa0 b18_cc4 b18_ca0 b18_220 w18_1334 w18_1330 w18_132c w18_1328 w18_1324 w18_1320 w18_131c w18_1318 w18_54 w18_40 w18_18 w18_14 w18_10 g18_26 g18_25 g18_24 g18_23 g18_22 g18_20 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 s18 X18 K18 P18
  -- 0xEBC: p2v_ude8Fs
  obtain ⟨n20, c20, s20, sp20, rk20, R1_20, R2_20, K20, fr20⟩ := p2v_ude8Fs (co := 0xC80) (ca := 0x200) (cb := 0xFE4) (ct := 0x1318) (s := ns)
    F E19 (UC0.p2v F fR19) s19 p2v_at_ebc p2v_at_ec0 (by decide) (by decide) g19_2
    g19_10 g19_11 g19_12 g19_13 g19_14 g19_15 g19_16 g19_17 hns1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [show 0x200 + 0x20 = 0x220 from rfl, b19_220]; exact hds)
    (by rw [show 0xFE4 + 0x20 = 0x1004 from rfl, b19_1004]; exact hes)
  obtain ⟨σ20a, A20a, hσ0_20, e0_20, bb0_20, vv0_20⟩ := R1_20
  simp only [p2vI, p2vM, show 0x200 + 0x20 = 0x220 from rfl, show 0xFE4 + 0x20 = 0x1004 from rfl,
    show 0x1318 + 0x0 = 0x1318 from rfl, show 0x1318 + 0x8 = 0x1320 from rfl] at e0_20
  rw [b19_220, a19_200, b19_1004, a19_fe4,
    acc2_frame w19_1318 w19_131c, acc2_frame w19_1320 w19_1324] at e0_20
  obtain ⟨σ20b, A20b, hσ1_20, e1_20, bb1_20, vv1_20⟩ := R2_20
  simp only [p2vI, p2vM, show 0x200 + 0x20 = 0x220 from rfl, show 0xFE4 + 0x20 = 0x1004 from rfl,
    show 0x1318 + 0x10 = 0x1328 from rfl, show 0x1318 + 0x18 = 0x1330 from rfl] at e1_20
  rw [b19_220, a19_200, b19_1004, a19_fe4,
    acc2_frame w19_1328 w19_132c, acc2_frame w19_1330 w19_1334] at e1_20
  rw [a19_980] at bb0_20 vv0_20 bb1_20 vv1_20
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, P2vR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : P2vCode n20.mem := E19.fr F fr20
  have V20 : P2vSaves B n20.mem v := V19.keepL K20 (by decide)
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk20 (3 : Fin 32) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk20 (4 : Fin 32) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk20 (8 : Fin 32) (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = BitVec.ofNat 32 ns := by rw [rk20 (9 : Fin 32) (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = qhi := by rw [rk20 (18 : Fin 32) (by decide), g19_18]
  have g20_20 : reg n20 (20 : Fin 32) = vlo := by rw [rk20 (20 : Fin 32) (by decide), g19_20]
  have g20_22 : reg n20 (22 : Fin 32) = rlo := by rw [rk20 (22 : Fin 32) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = ulo := by rw [rk20 (23 : Fin 32) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = dhi := by rw [rk20 (24 : Fin 32) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = vhi := by rw [rk20 (25 : Fin 32) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = uhi := by rw [rk20 (26 : Fin 32) (by decide), g19_26]
  have g20_2 : reg n20 sp = B + 0x21A0 := sp20
  have keep_kk20 : P2vKeepL B n0.mem n20.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24), (0x900, 0x24), (0xC80, 0x45)] := keep_kk19.trans K20
  clear keep_kk19
  have w20_10 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K20.w32 (by decide) (by decide)).trans w19_10
  have w20_14 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K20.w32 (by decide) (by decide)).trans w19_14
  have w20_18 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K20.w32 (by decide) (by decide)).trans w19_18
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K20.w32 (by decide) (by decide)).trans w19_40
  have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K20.w32 (by decide) (by decide)).trans w19_54
  have w20_1318 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K20.w32 (by decide) (by decide)).trans w19_1318
  have w20_131c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K20.w32 (by decide) (by decide)).trans w19_131c
  have w20_1320 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := (K20.w32 (by decide) (by decide)).trans w19_1320
  have w20_1324 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := (K20.w32 (by decide) (by decide)).trans w19_1324
  have w20_1328 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := (K20.w32 (by decide) (by decide)).trans w19_1328
  have w20_132c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := (K20.w32 (by decide) (by decide)).trans w19_132c
  have w20_1330 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := (K20.w32 (by decide) (by decide)).trans w19_1330
  have w20_1334 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := (K20.w32 (by decide) (by decide)).trans w19_1334
  have b20_220 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K20.b8 (by decide) (by decide)).trans b19_220
  have b20_920 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ14b := (K20.b8 (by decide) (by decide)).trans b19_920
  have b20_fa0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := (K20.b8 (by decide) (by decide)).trans b19_fa0
  have b20_1004 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K20.b8 (by decide) (by decide)).trans b19_1004
  have a20_180 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K20.acc (by decide) (by decide)).trans a19_180
  have a20_200 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K20.acc (by decide) (by decide)).trans a19_200
  have a20_900 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A14b / 2 ^ ns % 2 ^ 256 := (K20.acc (by decide) (by decide)).trans a19_900
  have a20_980 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K20.acc (by decide) (by decide)).trans a19_980
  have a20_f80 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := (K20.acc (by decide) (by decide)).trans a19_f80
  have a20_fe4 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K20.acc (by decide) (by decide)).trans a19_fe4
  have a20_1338 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K20.acc (by decide) (by decide)).trans a19_1338
  have a20_1358 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K20.acc (by decide) (by decide)).trans a19_1358
  have a20_c80 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := vv0_20
  have a20_ca4 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := vv1_20
  have b20_ca0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := byte_of_toNat bb0_20
  have b20_cc4 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := byte_of_toNat bb1_20
  clear a19_1358 a19_1338 a19_fe4 a19_f80 a19_ca4 a19_c80 a19_980 a19_900 a19_200 a19_180 b19_1004 b19_fa0 b19_cc4 b19_ca0 b19_920 b19_220 w19_1334 w19_1330 w19_132c w19_1328 w19_1324 w19_1320 w19_131c w19_1318 w19_54 w19_40 w19_18 w19_14 w19_10 g19_17 g19_16 g19_15 g19_14 g19_13 g19_12 g19_11 g19_10 g19_26 g19_25 g19_24 g19_23 g19_22 g19_20 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0xEC4
  obtain ⟨n21, c21, u21⟩ := s20.block p2vZBec4 E20.self p2vZBec4_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem P2V n21 0xED2 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock p2vZBec4 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
  have fr21 : ∀ x, P2vR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, P2vR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : P2vCode n21.mem := E20.fr F fr21
  have V21 : P2vSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by
    rw [rb21, runBlock_reg _ _ _ sp s20.zero (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (3 : Fin 32) s20.zero (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (4 : Fin 32) s20.zero (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb21, runBlock_reg _ _ _ (8 : Fin 32) s20.zero (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = qhi := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_20 : reg n21 (20 : Fin 32) = vlo := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_22 : reg n21 (22 : Fin 32) = rlo := by
    rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = ulo := by
    rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = dhi := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = vhi := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = uhi := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_10 : reg n21 a0 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, p2vZBec4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_20, g20_22, g20_23, g20_24, g20_25, g20_26, s20.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g21_11 : reg n21 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, p2vZBec4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_20, g20_22, g20_23, g20_24, g20_25, g20_26, s20.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g21_12 : reg n21 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, p2vZBec4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_20, g20_22, g20_23, g20_24, g20_25, g20_26, s20.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk21 : P2vKeepL B n0.mem n21.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24), (0x900, 0x24), (0xC80, 0x45)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_10 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m21]; exact w20_10
  have w21_14 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m21]; exact w20_14
  have w21_18 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m21]; exact w20_18
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m21]; exact w20_40
  have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m21]; exact w20_54
  have w21_1318 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m21]; exact w20_1318
  have w21_131c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m21]; exact w20_131c
  have w21_1320 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m21]; exact w20_1320
  have w21_1324 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m21]; exact w20_1324
  have w21_1328 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [m21]; exact w20_1328
  have w21_132c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [m21]; exact w20_132c
  have w21_1330 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [m21]; exact w20_1330
  have w21_1334 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [m21]; exact w20_1334
  have b21_220 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m21]; exact b20_220
  have b21_920 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ14b := by rw [m21]; exact b20_920
  have b21_ca0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m21]; exact b20_ca0
  have b21_cc4 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m21]; exact b20_cc4
  have b21_fa0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := by rw [m21]; exact b20_fa0
  have b21_1004 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m21]; exact b20_1004
  have a21_180 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m21]; exact a20_180
  have a21_200 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m21]; exact a20_200
  have a21_900 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A14b / 2 ^ ns % 2 ^ 256 := by rw [m21]; exact a20_900
  have a21_980 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m21]; exact a20_980
  have a21_c80 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m21]; exact a20_c80
  have a21_ca4 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m21]; exact a20_ca4
  have a21_f80 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := by rw [m21]; exact a20_f80
  have a21_fe4 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m21]; exact a20_fe4
  have a21_1338 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m21]; exact a20_1338
  have a21_1358 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m21]; exact a20_1358
  clear b20_cc4 b20_ca0 a20_ca4 a20_c80 a20_1358 a20_1338 a20_fe4 a20_f80 a20_980 a20_900 a20_200 a20_180 b20_1004 b20_fa0 b20_920 b20_220 w20_1334 w20_1330 w20_132c w20_1328 w20_1324 w20_1320 w20_131c w20_1318 w20_54 w20_40 w20_18 w20_14 w20_10 g20_2 g20_26 g20_25 g20_24 g20_23 g20_22 g20_20 g20_18 g20_9 g20_8 g20_4 g20_3 V20 E20 fR20 t20 vv1_20 bb1_20 vv0_20 bb0_20 fr20 K20 rk20 sp20 s20 c20
  -- 0xED2: memcpy
  obtain ⟨n22, P22, K22, X22⟩ := p2v_mc (c := 0x200) (d := 0xC80) (N := 0x24) F E21 s21 p2v_at_ed2 p2v_at_ed6
    (by decide) (by decide) g21_2 g21_10 g21_11 g21_12
    (by decide) (by decide) (by decide)
  have s22 := P22.st
  have fr22 := P22.fr
  have t22 : Steps n0 n22 := t21.trans P22.steps
  have fR22 : ∀ x, P2vR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : P2vCode n22.mem := E21.fr F fr22
  have V22 : P2vSaves B n22.mem v := V21.keep K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [P22.regs sp (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P22.regs (3 : Fin 32) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P22.regs (4 : Fin 32) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P22.regs (8 : Fin 32) (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = BitVec.ofNat 32 ns := by rw [P22.regs (9 : Fin 32) (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = qhi := by rw [P22.regs (18 : Fin 32) (by decide), g21_18]
  have g22_20 : reg n22 (20 : Fin 32) = vlo := by rw [P22.regs (20 : Fin 32) (by decide), g21_20]
  have g22_22 : reg n22 (22 : Fin 32) = rlo := by rw [P22.regs (22 : Fin 32) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = ulo := by rw [P22.regs (23 : Fin 32) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = dhi := by rw [P22.regs (24 : Fin 32) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = vhi := by rw [P22.regs (25 : Fin 32) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = uhi := by rw [P22.regs (26 : Fin 32) (by decide), g21_26]
  have keep_kk22 : P2vKeepL B n0.mem n22.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24), (0x900, 0x24), (0xC80, 0x45), (0x200, 0x24)] := keep_kk21.trans K22.toL
  clear keep_kk21
  have w22_10 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K22.w32 (by decide) (by decide)).trans w21_10
  have w22_14 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K22.w32 (by decide) (by decide)).trans w21_14
  have w22_18 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K22.w32 (by decide) (by decide)).trans w21_18
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K22.w32 (by decide) (by decide)).trans w21_40
  have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K22.w32 (by decide) (by decide)).trans w21_54
  have w22_1318 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K22.w32 (by decide) (by decide)).trans w21_1318
  have w22_131c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K22.w32 (by decide) (by decide)).trans w21_131c
  have w22_1320 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := (K22.w32 (by decide) (by decide)).trans w21_1320
  have w22_1324 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := (K22.w32 (by decide) (by decide)).trans w21_1324
  have w22_1328 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := (K22.w32 (by decide) (by decide)).trans w21_1328
  have w22_132c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := (K22.w32 (by decide) (by decide)).trans w21_132c
  have w22_1330 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := (K22.w32 (by decide) (by decide)).trans w21_1330
  have w22_1334 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := (K22.w32 (by decide) (by decide)).trans w21_1334
  have b22_920 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ14b := (K22.b8 (by decide) (by decide)).trans b21_920
  have b22_ca0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := (K22.b8 (by decide) (by decide)).trans b21_ca0
  have b22_cc4 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := (K22.b8 (by decide) (by decide)).trans b21_cc4
  have b22_fa0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := (K22.b8 (by decide) (by decide)).trans b21_fa0
  have b22_1004 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K22.b8 (by decide) (by decide)).trans b21_1004
  have b22_220 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [show 0x220 = 0x200 + 0x20 from rfl, X22 0x20 (by decide)]; exact b21_ca0
  have a22_180 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K22.acc (by decide) (by decide)).trans a21_180
  have a22_900 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A14b / 2 ^ ns % 2 ^ 256 := (K22.acc (by decide) (by decide)).trans a21_900
  have a22_980 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K22.acc (by decide) (by decide)).trans a21_980
  have a22_c80 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := (K22.acc (by decide) (by decide)).trans a21_c80
  have a22_ca4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := (K22.acc (by decide) (by decide)).trans a21_ca4
  have a22_f80 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := (K22.acc (by decide) (by decide)).trans a21_f80
  have a22_fe4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K22.acc (by decide) (by decide)).trans a21_fe4
  have a22_1338 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K22.acc (by decide) (by decide)).trans a21_1338
  have a22_1358 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K22.acc (by decide) (by decide)).trans a21_1358
  have a22_200 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := (accV_S 8 fun q hq => by
    rw [show 0x200 + q = 0x200 + (0x0 + q) by omega, X22 (0x0 + q) (by omega),
      show 0xC80 + (0x0 + q) = 0xC80 + q by omega]).trans a21_c80
  clear a21_1358 a21_1338 a21_fe4 a21_f80 a21_ca4 a21_c80 a21_980 a21_900 a21_200 a21_180 b21_1004 b21_fa0 b21_cc4 b21_ca0 b21_920 b21_220 w21_1334 w21_1330 w21_132c w21_1328 w21_1324 w21_1320 w21_131c w21_1318 w21_54 w21_40 w21_18 w21_14 w21_10 g21_12 g21_11 g21_10 g21_26 g21_25 g21_24 g21_23 g21_22 g21_20 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0xEDA
  obtain ⟨n23, c23, u23⟩ := s22.block p2vZBeda E22.self p2vZBeda_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem P2V n23 0xEEE (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock p2vZBeda (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
  have fr23 : ∀ x, P2vR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans c23
  have fR23 : ∀ x, P2vR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : P2vCode n23.mem := E22.fr F fr23
  have V23 : P2vSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by
    rw [rb23, runBlock_reg _ _ _ sp s22.zero (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (3 : Fin 32) s22.zero (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (4 : Fin 32) s22.zero (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = qhi := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_20 : reg n23 (20 : Fin 32) = vlo := by
    rw [rb23, runBlock_reg _ _ _ (20 : Fin 32) s22.zero (by decide), g22_20]
  have g23_22 : reg n23 (22 : Fin 32) = rlo := by
    rw [rb23, runBlock_reg _ _ _ (22 : Fin 32) s22.zero (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = ulo := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = dhi := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = vhi := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = uhi := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_10 : reg n23 a0 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vZBeda, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_20, g22_22, g22_23, g22_24, g22_25, g22_26, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g23_11 : reg n23 a1 = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vZBeda, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_20, g22_22, g22_23, g22_24, g22_25, g22_26, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g23_12 : reg n23 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vZBeda, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_20, g22_22, g22_23, g22_24, g22_25, g22_26, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk23 : P2vKeepL B n0.mem n23.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24), (0x900, 0x24), (0xC80, 0x45), (0x200, 0x24)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_10 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m23]; exact w22_10
  have w23_14 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m23]; exact w22_14
  have w23_18 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m23]; exact w22_18
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m23]; exact w22_40
  have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m23]; exact w22_54
  have w23_1318 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m23]; exact w22_1318
  have w23_131c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m23]; exact w22_131c
  have w23_1320 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m23]; exact w22_1320
  have w23_1324 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m23]; exact w22_1324
  have w23_1328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [m23]; exact w22_1328
  have w23_132c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [m23]; exact w22_132c
  have w23_1330 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [m23]; exact w22_1330
  have w23_1334 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [m23]; exact w22_1334
  have b23_220 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m23]; exact b22_220
  have b23_920 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ14b := by rw [m23]; exact b22_920
  have b23_ca0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m23]; exact b22_ca0
  have b23_cc4 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m23]; exact b22_cc4
  have b23_fa0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := by rw [m23]; exact b22_fa0
  have b23_1004 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m23]; exact b22_1004
  have a23_180 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m23]; exact a22_180
  have a23_200 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m23]; exact a22_200
  have a23_900 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A14b / 2 ^ ns % 2 ^ 256 := by rw [m23]; exact a22_900
  have a23_980 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m23]; exact a22_980
  have a23_c80 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m23]; exact a22_c80
  have a23_ca4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m23]; exact a22_ca4
  have a23_f80 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := by rw [m23]; exact a22_f80
  have a23_fe4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m23]; exact a22_fe4
  have a23_1338 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m23]; exact a22_1338
  have a23_1358 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m23]; exact a22_1358
  clear a22_200 a22_1358 a22_1338 a22_fe4 a22_f80 a22_ca4 a22_c80 a22_980 a22_900 a22_180 b22_220 b22_1004 b22_fa0 b22_cc4 b22_ca0 b22_920 w22_1334 w22_1330 w22_132c w22_1328 w22_1324 w22_1320 w22_131c w22_1318 w22_54 w22_40 w22_18 w22_14 w22_10 g22_26 g22_25 g22_24 g22_23 g22_22 g22_20 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 s22 X22 K22 P22
  -- 0xEEE: memcpy
  obtain ⟨n24, P24, K24, X24⟩ := p2v_mc (c := 0xFE4) (d := 0xCA4) (N := 0x24) F E23 s23 p2v_at_eee p2v_at_ef2
    (by decide) (by decide) g23_2 g23_10 g23_11 g23_12
    (by decide) (by decide) (by decide)
  have s24 := P24.st
  have fr24 := P24.fr
  have t24 : Steps n0 n24 := t23.trans P24.steps
  have fR24 : ∀ x, P2vR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : P2vCode n24.mem := E23.fr F fr24
  have V24 : P2vSaves B n24.mem v := V23.keep K24 (by decide)
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [P24.regs sp (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P24.regs (3 : Fin 32) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P24.regs (4 : Fin 32) (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P24.regs (8 : Fin 32) (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = BitVec.ofNat 32 ns := by rw [P24.regs (9 : Fin 32) (by decide), g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = qhi := by rw [P24.regs (18 : Fin 32) (by decide), g23_18]
  have g24_20 : reg n24 (20 : Fin 32) = vlo := by rw [P24.regs (20 : Fin 32) (by decide), g23_20]
  have g24_22 : reg n24 (22 : Fin 32) = rlo := by rw [P24.regs (22 : Fin 32) (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = ulo := by rw [P24.regs (23 : Fin 32) (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = dhi := by rw [P24.regs (24 : Fin 32) (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = vhi := by rw [P24.regs (25 : Fin 32) (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = uhi := by rw [P24.regs (26 : Fin 32) (by decide), g23_26]
  have keep_kk24 : P2vKeepL B n0.mem n24.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24), (0x900, 0x24), (0xC80, 0x45), (0x200, 0x24), (0xFE4, 0x24)] := keep_kk23.trans K24.toL
  clear keep_kk23
  have w24_10 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K24.w32 (by decide) (by decide)).trans w23_10
  have w24_14 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := (K24.w32 (by decide) (by decide)).trans w23_14
  have w24_18 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := (K24.w32 (by decide) (by decide)).trans w23_18
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K24.w32 (by decide) (by decide)).trans w23_40
  have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := (K24.w32 (by decide) (by decide)).trans w23_54
  have w24_1318 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := (K24.w32 (by decide) (by decide)).trans w23_1318
  have w24_131c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := (K24.w32 (by decide) (by decide)).trans w23_131c
  have w24_1320 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := (K24.w32 (by decide) (by decide)).trans w23_1320
  have w24_1324 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := (K24.w32 (by decide) (by decide)).trans w23_1324
  have w24_1328 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := (K24.w32 (by decide) (by decide)).trans w23_1328
  have w24_132c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := (K24.w32 (by decide) (by decide)).trans w23_132c
  have w24_1330 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := (K24.w32 (by decide) (by decide)).trans w23_1330
  have w24_1334 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := (K24.w32 (by decide) (by decide)).trans w23_1334
  have b24_220 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := (K24.b8 (by decide) (by decide)).trans b23_220
  have b24_920 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ14b := (K24.b8 (by decide) (by decide)).trans b23_920
  have b24_ca0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := (K24.b8 (by decide) (by decide)).trans b23_ca0
  have b24_cc4 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := (K24.b8 (by decide) (by decide)).trans b23_cc4
  have b24_fa0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := (K24.b8 (by decide) (by decide)).trans b23_fa0
  have b24_1004 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [show 0x1004 = 0xFE4 + 0x20 from rfl, X24 0x20 (by decide)]; exact b23_cc4
  have a24_180 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K24.acc (by decide) (by decide)).trans a23_180
  have a24_200 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := (K24.acc (by decide) (by decide)).trans a23_200
  have a24_900 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A14b / 2 ^ ns % 2 ^ 256 := (K24.acc (by decide) (by decide)).trans a23_900
  have a24_980 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K24.acc (by decide) (by decide)).trans a23_980
  have a24_c80 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := (K24.acc (by decide) (by decide)).trans a23_c80
  have a24_ca4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := (K24.acc (by decide) (by decide)).trans a23_ca4
  have a24_f80 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := (K24.acc (by decide) (by decide)).trans a23_f80
  have a24_1338 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K24.acc (by decide) (by decide)).trans a23_1338
  have a24_1358 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K24.acc (by decide) (by decide)).trans a23_1358
  have a24_fe4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := (accV_S 8 fun q hq => by
    rw [show 0xFE4 + q = 0xFE4 + (0x0 + q) by omega, X24 (0x0 + q) (by omega),
      show 0xCA4 + (0x0 + q) = 0xCA4 + q by omega]).trans a23_ca4
  clear a23_1358 a23_1338 a23_fe4 a23_f80 a23_ca4 a23_c80 a23_980 a23_900 a23_200 a23_180 b23_1004 b23_fa0 b23_cc4 b23_ca0 b23_920 b23_220 w23_1334 w23_1330 w23_132c w23_1328 w23_1324 w23_1320 w23_131c w23_1318 w23_54 w23_40 w23_18 w23_14 w23_10 g23_12 g23_11 g23_10 g23_26 g23_25 g23_24 g23_23 g23_22 g23_20 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0xEF6
  obtain ⟨n25, c25, u25⟩ := s24.block p2vZBef6 E24.self p2vZBef6_end
    ⟨trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem P2V n25 0xEF8 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock p2vZBef6 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
  have fr25 : ∀ x, P2vR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, P2vR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : P2vCode n25.mem := E24.fr F fr25
  have V25 : P2vSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by
    rw [rb25, runBlock_reg _ _ _ sp s24.zero (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb25, runBlock_reg _ _ _ (3 : Fin 32) s24.zero (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb25, runBlock_reg _ _ _ (4 : Fin 32) s24.zero (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = qhi := by
    rw [rb25, runBlock_reg _ _ _ (18 : Fin 32) s24.zero (by decide), g24_18]
  have g25_20 : reg n25 (20 : Fin 32) = vlo := by
    rw [rb25, runBlock_reg _ _ _ (20 : Fin 32) s24.zero (by decide), g24_20]
  have g25_22 : reg n25 (22 : Fin 32) = rlo := by
    rw [rb25, runBlock_reg _ _ _ (22 : Fin 32) s24.zero (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = ulo := by
    rw [rb25, runBlock_reg _ _ _ (23 : Fin 32) s24.zero (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = dhi := by
    rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = vhi := by
    rw [rb25, runBlock_reg _ _ _ (25 : Fin 32) s24.zero (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = uhi := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_14 : reg n25 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, p2vZBef6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_20, g24_22, g24_23, g24_24, g24_25, g24_26, s24.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk25 : P2vKeepL B n0.mem n25.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24), (0x900, 0x24), (0xC80, 0x45), (0x200, 0x24), (0xFE4, 0x24)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_10 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m25]; exact w24_10
  have w25_14 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m25]; exact w24_14
  have w25_18 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m25]; exact w24_18
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m25]; exact w24_40
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m25]; exact w24_54
  have w25_1318 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m25]; exact w24_1318
  have w25_131c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m25]; exact w24_131c
  have w25_1320 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m25]; exact w24_1320
  have w25_1324 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m25]; exact w24_1324
  have w25_1328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [m25]; exact w24_1328
  have w25_132c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [m25]; exact w24_132c
  have w25_1330 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [m25]; exact w24_1330
  have w25_1334 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [m25]; exact w24_1334
  have b25_220 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m25]; exact b24_220
  have b25_920 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ14b := by rw [m25]; exact b24_920
  have b25_ca0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m25]; exact b24_ca0
  have b25_cc4 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m25]; exact b24_cc4
  have b25_fa0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := by rw [m25]; exact b24_fa0
  have b25_1004 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m25]; exact b24_1004
  have a25_180 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m25]; exact a24_180
  have a25_200 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m25]; exact a24_200
  have a25_900 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A14b / 2 ^ ns % 2 ^ 256 := by rw [m25]; exact a24_900
  have a25_980 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m25]; exact a24_980
  have a25_c80 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m25]; exact a24_c80
  have a25_ca4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m25]; exact a24_ca4
  have a25_f80 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := by rw [m25]; exact a24_f80
  have a25_fe4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m25]; exact a24_fe4
  have a25_1338 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m25]; exact a24_1338
  have a25_1358 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m25]; exact a24_1358
  clear a24_fe4 a24_1358 a24_1338 a24_f80 a24_ca4 a24_c80 a24_980 a24_900 a24_200 a24_180 b24_1004 b24_fa0 b24_cc4 b24_ca0 b24_920 b24_220 w24_1334 w24_1330 w24_132c w24_1328 w24_1324 w24_1320 w24_131c w24_1318 w24_54 w24_40 w24_18 w24_14 w24_10 g24_26 g24_25 g24_24 g24_23 g24_22 g24_20 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 s24 X24 K24 P24
  -- 0xEF8: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self p2v_at_ef8 (off' := 0xEFA) (by decide)
    (by rw [g25_2, show B + 0x21A0 + 0x18 = B + 0x21A0 + BitVec.ofNat 32 0x18 by p2v_addr]; exact p2v_al F (by decide) (by decide))
  have s26 : St n26.mem P2V n26 0xEFA (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, P2vR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, P2vR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : P2vCode n26.mem := E25.fr F fr26
  have V26 : P2vSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = BitVec.ofNat 32 ns := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
  have g26_14 : reg n26 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_14]
  have g26_18 : reg n26 (18 : Fin 32) = qhi := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_20 : reg n26 (20 : Fin 32) = vlo := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
  have g26_22 : reg n26 (22 : Fin 32) = rlo := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = ulo := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = dhi := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = vhi := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = uhi := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_10 : reg n26 a0 = rem := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_2, show B + 0x21A0 + 0x18 = B + 0x21A0 + BitVec.ofNat 32 0x18 by p2v_addr, w25_18]
  have keep_kk26 : P2vKeepL B n0.mem n26.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24), (0x900, 0x24), (0xC80, 0x45), (0x200, 0x24), (0xFE4, 0x24)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_10 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m26]; exact w25_10
  have w26_14 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m26]; exact w25_14
  have w26_18 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m26]; exact w25_18
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m26]; exact w25_40
  have w26_54 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m26]; exact w25_54
  have w26_1318 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m26]; exact w25_1318
  have w26_131c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m26]; exact w25_131c
  have w26_1320 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m26]; exact w25_1320
  have w26_1324 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m26]; exact w25_1324
  have w26_1328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [m26]; exact w25_1328
  have w26_132c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [m26]; exact w25_132c
  have w26_1330 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [m26]; exact w25_1330
  have w26_1334 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [m26]; exact w25_1334
  have b26_220 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m26]; exact b25_220
  have b26_920 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ14b := by rw [m26]; exact b25_920
  have b26_ca0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m26]; exact b25_ca0
  have b26_cc4 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m26]; exact b25_cc4
  have b26_fa0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := by rw [m26]; exact b25_fa0
  have b26_1004 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m26]; exact b25_1004
  have a26_180 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m26]; exact a25_180
  have a26_200 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m26]; exact a25_200
  have a26_900 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A14b / 2 ^ ns % 2 ^ 256 := by rw [m26]; exact a25_900
  have a26_980 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m26]; exact a25_980
  have a26_c80 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m26]; exact a25_c80
  have a26_ca4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m26]; exact a25_ca4
  have a26_f80 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := by rw [m26]; exact a25_f80
  have a26_fe4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m26]; exact a25_fe4
  have a26_1338 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m26]; exact a25_1338
  have a26_1358 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m26]; exact a25_1358
  clear a25_1358 a25_1338 a25_fe4 a25_f80 a25_ca4 a25_c80 a25_980 a25_900 a25_200 a25_180 b25_1004 b25_fa0 b25_cc4 b25_ca0 b25_920 b25_220 w25_1334 w25_1330 w25_132c w25_1328 w25_1324 w25_1320 w25_131c w25_1318 w25_54 w25_40 w25_18 w25_14 w25_10 g25_14 g25_26 g25_25 g25_24 g25_23 g25_22 g25_20 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0xEFA
  obtain ⟨n27, c27, u27⟩ := s26.block p2vZBefa E26.self p2vZBefa_end
    ⟨trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem P2V n27 0xEFC (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock p2vZBefa (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
  have fr27 : ∀ x, P2vR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans c27
  have fR27 : ∀ x, P2vR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : P2vCode n27.mem := E26.fr F fr27
  have V27 : P2vSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by
    rw [rb27, runBlock_reg _ _ _ sp s26.zero (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (3 : Fin 32) s26.zero (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (4 : Fin 32) s26.zero (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb27, runBlock_reg _ _ _ (9 : Fin 32) s26.zero (by decide), g26_9]
  have g27_14 : reg n27 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb27, runBlock_reg _ _ _ a4 s26.zero (by decide), g26_14]
  have g27_18 : reg n27 (18 : Fin 32) = qhi := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_20 : reg n27 (20 : Fin 32) = vlo := by
    rw [rb27, runBlock_reg _ _ _ (20 : Fin 32) s26.zero (by decide), g26_20]
  have g27_22 : reg n27 (22 : Fin 32) = rlo := by
    rw [rb27, runBlock_reg _ _ _ (22 : Fin 32) s26.zero (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = ulo := by
    rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = dhi := by
    rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = vhi := by
    rw [rb27, runBlock_reg _ _ _ (25 : Fin 32) s26.zero (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = uhi := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_10 : reg n27 a0 = (rem) - (BitVec.ofNat 32 ns) := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, p2vZBefa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_10, g26_14, g26_18, g26_20, g26_22, g26_23, g26_24, g26_25, g26_26, s26.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk27 : P2vKeepL B n0.mem n27.mem [(0x1318, 0x4), (0x131C, 0x4), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0xC80, 0x45), (0xF80, 0x24), (0x900, 0x24), (0xC80, 0x45), (0x200, 0x24), (0xFE4, 0x24)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_10 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m27]; exact w26_10
  have w27_14 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 ns := by rw [m27]; exact w26_14
  have w27_18 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = rem := by rw [m27]; exact w26_18
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m27]; exact w26_40
  have w27_54 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = qlo := by rw [m27]; exact w26_54
  have w27_1318 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1318) = ulo := by rw [m27]; exact w26_1318
  have w27_131c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x131C) = uhi := by rw [m27]; exact w26_131c
  have w27_1320 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = vlo := by rw [m27]; exact w26_1320
  have w27_1324 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = vhi := by rw [m27]; exact w26_1324
  have w27_1328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = qlo := by rw [m27]; exact w26_1328
  have w27_132c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = qhi := by rw [m27]; exact w26_132c
  have w27_1330 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = rlo := by rw [m27]; exact w26_1330
  have w27_1334 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = rhi := by rw [m27]; exact w26_1334
  have b27_220 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m27]; exact b26_220
  have b27_920 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = BitVec.ofNat 8 σ14b := by rw [m27]; exact b26_920
  have b27_ca0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = BitVec.ofNat 8 (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m27]; exact b26_ca0
  have b27_cc4 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m27]; exact b26_cc4
  have b27_fa0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = BitVec.ofNat 8 σ14a := by rw [m27]; exact b26_fa0
  have b27_1004 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = BitVec.ofNat 8 (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).1 := by rw [m27]; exact b26_1004
  have a27_180 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m27]; exact a26_180
  have a27_200 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m27]; exact a26_200
  have a27_900 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = A14b / 2 ^ ns % 2 ^ 256 := by rw [m27]; exact a26_900
  have a27_980 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m27]; exact a26_980
  have a27_c80 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (lrsm8 σ20a A20a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m27]; exact a26_c80
  have a27_ca4 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m27]; exact a26_ca4
  have a27_f80 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = A14a / 2 ^ ns % 2 ^ 256 := by rw [m27]; exact a26_f80
  have a27_fe4 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (lrsm8 σ20b A20b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)).2 := by rw [m27]; exact a26_fe4
  have a27_1338 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m27]; exact a26_1338
  have a27_1358 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m27]; exact a26_1358
  clear a26_1358 a26_1338 a26_fe4 a26_f80 a26_ca4 a26_c80 a26_980 a26_900 a26_200 a26_180 b26_1004 b26_fa0 b26_cc4 b26_ca0 b26_920 b26_220 w26_1334 w26_1330 w26_132c w26_1328 w26_1324 w26_1320 w26_131c w26_1318 w26_54 w26_40 w26_18 w26_14 w26_10 g26_10 g26_26 g26_25 g26_24 g26_23 g26_22 g26_20 g26_18 g26_14 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  exact .inr ⟨σ14a, A14a, e0_14, hσ0_14, σ14b, A14b, e1_14, hσ1_14, σ20a, A20a, e0_20, hσ0_20, σ20b, A20b, e1_20, hσ1_20, n27, t27, s27, E27, V27, fR27, g27_2, g27_3, g27_4, g27_10, g27_14, g27_24, w27_10, w27_40, b27_220, b27_920, b27_ca0, b27_cc4, b27_fa0, b27_1004, a27_180, a27_200, a27_900, a27_980, a27_c80, a27_ca4, a27_f80, a27_fe4, a27_1338, a27_1358, keep_kk27.mono (by decide)⟩

end C3.RV32.P2v
