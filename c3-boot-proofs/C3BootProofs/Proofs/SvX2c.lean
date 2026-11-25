import C3BootProofs.Proofs.SvData

/-!
# `sigstore::verify`: a critical extension's value

From the criticality test at 0x42C to the table of critical OIDs at 0x4BE, for a critical extension: `BOOLEAN TRUE`, and a value that ends it, with an OID that isn't an earlier extension's.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svX2c436 : List BInstr :=
  [.aluImm .add a1 x0 0x1]
theorem svX2c436_end : blockEnd sigstoreVerifyCode 0x436 svX2c436 = some 0x438 := by
  simp only [svX2c436]
  rw [blockEnd, sv_at_436]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2c43c : List BInstr :=
  [.aluImm .add a0 sp 0x400]
theorem svX2c43c_end : blockEnd sigstoreVerifyCode 0x43C svX2c43c = some 0x440 := by
  simp only [svX2c43c]
  rw [blockEnd, sv_at_43c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2c44a : List BInstr :=
  [.aluImm .and a0 a0 0xFF, .aluImm .add a0 a0 0xFFFFFF01]
theorem svX2c44a_end : blockEnd sigstoreVerifyCode 0x44A svX2c44a = some 0x452 := by
  simp only [svX2c44a]
  rw [blockEnd, sv_at_44a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_44e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2c456 : List BInstr :=
  [.aluImm .add (26 : Fin 32) x0 0x1]
theorem svX2c456_end : blockEnd sigstoreVerifyCode 0x456 svX2c456 = some 0x458 := by
  simp only [svX2c456]
  rw [blockEnd, sv_at_456]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2c45c : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x400]
theorem svX2c45c_end : blockEnd sigstoreVerifyCode 0x45C svX2c45c = some 0x464 := by
  simp only [svX2c45c]
  rw [blockEnd, sv_at_45c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_460]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2c940 : List BInstr :=
  [.aluImm .add a0 x0 0x1]
theorem svX2c940_end : blockEnd sigstoreVerifyCode 0x940 svX2c940 = some 0x942 := by
  simp only [svX2c940]
  rw [blockEnd, sv_at_940]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2c488 : List BInstr :=
  [.alu .sub a1 a1 a0]
theorem svX2c488_end : blockEnd sigstoreVerifyCode 0x488 svX2c488 = some 0x48A := by
  simp only [svX2c488]
  rw [blockEnd, sv_at_488]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2c498 : List BInstr :=
  [.aluImm .and a0 a0 0x1]
theorem svX2c498_end : blockEnd sigstoreVerifyCode 0x498 svX2c498 = some 0x49A := by
  simp only [svX2c498]
  rw [blockEnd, sv_at_498]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2c4a2 : List BInstr :=
  [.aluImm .and a0 a0 0x1, .aluImm .add a1 x0 0x16]
theorem svX2c4a2_end : blockEnd sigstoreVerifyCode 0x4A2 svX2c4a2 = some 0x4A6 := by
  simp only [svX2c4a2]
  rw [blockEnd, sv_at_4a2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_4a4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2c4b0 : List BInstr :=
  [.aluImm .add a0 x0 0x20]
theorem svX2c4b0_end : blockEnd sigstoreVerifyCode 0x4B0 svX2c4b0 = some 0x4B4 := by
  simp only [svX2c4b0]
  rw [blockEnd, sv_at_4b0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2c4b6 : List BInstr :=
  [.lui (26 : Fin 32) 0x3FCC5000, .aluImm .add (26 : Fin 32) (26 : Fin 32) 0xFFFFF908]
theorem svX2c4b6_end : blockEnd sigstoreVerifyCode 0x4B6 svX2c4b6 = some 0x4BE := by
  simp only [svX2c4b6]
  rw [blockEnd, sv_at_4b6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_4ba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_x2c {B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c rem2 ol op rest rp2 : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x42C (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = tbp)
    (g0_10 : reg n0 a0 = rem2)
    (g0_11 : reg n0 a1 = ol)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = dg)
    (g0_21 : reg n0 (21 : Fin 32) = rootp)
    (g0_22 : reg n0 (22 : Fin 32) = ll)
    (g0_23 : reg n0 (23 : Fin 32) = sgp)
    (g0_24 : reg n0 (24 : Fin 32) = kp)
    (g0_25 : reg n0 (25 : Fin 32) = sgl)
    (g0_27 : reg n0 (27 : Fin 32) = tbl)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54)
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c)
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5)
    (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6)
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7)
    (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8)
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9)
    (w0_150 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0)
    (w0_154 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op)
    (w0_158 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur)
    (w0_15c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest)
    (w0_408 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = rp2)
    (w0_40c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = rem2)
    (in2 : SvIn B rp2 rem2.toNat)
    (oid_in : SvIn B op ol.toNat)
    (ea_in : SvIn B p0 (L.toNat - rem.toNat))
    (hle : rem.toNat ≤ L.toNat)
    (hr2 : rem2 ≠ 0)
    (hb1 : M0 rp2 = BitVec.ofNat 8 1)
    (SD0 : SvData M0) :
    (¬ (derBoolOf (memBytes M0 (rp2) (rem2).toNat) (derElement 1 (memBytes M0 (rp2) (rem2).toNat)) = .ok () ∧ ∃ tb7, derElement 1 (memBytes M0 (rp2) (rem2).toNat) = .ok tb7 ∧ ∃ vp14 vl14, derContent ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) (derElement 4 (memBytes M0 ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)).toNat)) = .ok (vp14, vl14) ∧ ∃ te14, derElement 4 (memBytes M0 ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)).toNat) = .ok te14 ∧ (((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op ol.toNat) = .ok false ∧ True) ∧ SvErrRet B out v n0) ∨
    (derBoolOf (memBytes M0 (rp2) (rem2).toNat) (derElement 1 (memBytes M0 (rp2) (rem2).toNat)) = .ok () ∧
    ∃ tb7, derElement 1 (memBytes M0 (rp2) (rem2).toNat) = .ok tb7 ∧
    ∃ vp14 vl14, derContent ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) (derElement 4 (memBytes M0 ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)).toNat)) = .ok (vp14, vl14) ∧
    ∃ te14, derElement 4 (memBytes M0 ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)).toNat) = .ok te14 ∧
    (((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) = 0) ∧
    listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op ol.toNat) = .ok false ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x4BE (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = tbp ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (23 : Fin 32) = sgp ∧
        reg n' (24 : Fin 32) = kp ∧
        reg n' (25 : Fin 32) = sgl ∧
        reg n' (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x11) ∧
        reg n' (27 : Fin 32) = tbl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest ∧
        SvKeepL B n0.mem n'.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4), (0x50, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x42C: branch, not taken
  obtain ⟨n1, d1, u1⟩ := s0.notTaken E0.self 0x42E sv_at_42c
    (by decide) (by rw [g0_10, s0.zero]; exact br_beq_f hr2)
  have s1 : St n1.mem SV n1 0x42E (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, g0_4]
  have g1_9 : reg n1 (9 : Fin 32) = tbp := by rw [u1.regs, g0_9]
  have g1_10 : reg n1 a0 = rem2 := by rw [u1.regs, g0_10]
  have g1_11 : reg n1 a1 = ol := by rw [u1.regs, g0_11]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = dg := by rw [u1.regs, g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = rootp := by rw [u1.regs, g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = ll := by rw [u1.regs, g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = sgp := by rw [u1.regs, g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = kp := by rw [u1.regs, g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = sgl := by rw [u1.regs, g0_25]
  have g1_27 : reg n1 (27 : Fin 32) = tbl := by rw [u1.regs, g0_27]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m1]; exact w0_2c
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m1]; exact w0_30
  have w1_3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m1]; exact w0_3c
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m1]; exact w0_40
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m1]; exact w0_48
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m1]; exact w0_4c
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m1]; exact w0_50
  have w1_54 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m1]; exact w0_54
  have w1_58 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m1]; exact w0_58
  have w1_5c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m1]; exact w0_5c
  have w1_60 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m1]; exact w0_60
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m1]; exact w0_64
  have w1_68 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m1]; exact w0_68
  have w1_6c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m1]; exact w0_6c
  have w1_70 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m1]; exact w0_70
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m1]; exact w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m1]; exact w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m1]; exact w0_7c
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m1]; exact w0_80
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m1]; exact w0_84
  have w1_88 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m1]; exact w0_88
  have w1_8c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m1]; exact w0_8c
  have w1_90 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m1]; exact w0_90
  have w1_94 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m1]; exact w0_94
  have w1_98 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m1]; exact w0_98
  have w1_9c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m1]; exact w0_9c
  have w1_a0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m1]; exact w0_a0
  have w1_a4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m1]; exact w0_a4
  have w1_150 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m1]; exact w0_150
  have w1_154 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m1]; exact w0_154
  have w1_158 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m1]; exact w0_158
  have w1_15c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m1]; exact w0_15c
  have w1_408 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = rp2 := by rw [m1]; exact w0_408
  have w1_40c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = rem2 := by rw [m1]; exact w0_40c
  -- 0x42E: lw
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_42e (off' := 0x432) (by decide)
    (by rw [g1_2, show B + 0x21A0 + 0x408 = B + 0x21A0 + BitVec.ofNat 32 0x408 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s2 : St n2.mem SV n2 0x432 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_9 : reg n2 (9 : Fin 32) = tbp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_9]
  have g2_11 : reg n2 a1 = ol := by rw [u2.regs, upd_ne (by decide) (by decide), g1_11]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = sgp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = kp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = sgl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_27 : reg n2 (27 : Fin 32) = tbl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_10 : reg n2 a0 = rp2 := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_2, show B + 0x21A0 + 0x408 = B + 0x21A0 + BitVec.ofNat 32 0x408 by sv_addr, w1_408]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m2]; exact w1_2c
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m2]; exact w1_30
  have w2_3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m2]; exact w1_3c
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m2]; exact w1_40
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m2]; exact w1_48
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m2]; exact w1_4c
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m2]; exact w1_50
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m2]; exact w1_54
  have w2_58 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m2]; exact w1_58
  have w2_5c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m2]; exact w1_5c
  have w2_60 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m2]; exact w1_60
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m2]; exact w1_64
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m2]; exact w1_68
  have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m2]; exact w1_6c
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m2]; exact w1_70
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m2]; exact w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m2]; exact w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m2]; exact w1_7c
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m2]; exact w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m2]; exact w1_84
  have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m2]; exact w1_88
  have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m2]; exact w1_8c
  have w2_90 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m2]; exact w1_90
  have w2_94 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m2]; exact w1_94
  have w2_98 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m2]; exact w1_98
  have w2_9c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m2]; exact w1_9c
  have w2_a0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m2]; exact w1_a0
  have w2_a4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m2]; exact w1_a4
  have w2_150 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m2]; exact w1_150
  have w2_154 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m2]; exact w1_154
  have w2_158 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m2]; exact w1_158
  have w2_15c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m2]; exact w1_15c
  have w2_408 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = rp2 := by rw [m2]; exact w1_408
  have w2_40c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = rem2 := by rw [m2]; exact w1_40c
  clear w1_40c w1_408 w1_15c w1_158 w1_154 w1_150 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_40 w1_3c w1_30 w1_2c g1_27 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_11 g1_10 g1_9 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x432: lbu from the bundle
  obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_432 (off' := 0x436) (by decide)
  have s3 : St n3.mem SV n3 0x436 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_9 : reg n3 (9 : Fin 32) = tbp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_11 : reg n3 a1 = ol := by rw [u3.regs, upd_ne (by decide) (by decide), g2_11]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = sgp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = kp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = sgl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_27 : reg n3 (27 : Fin 32) = tbl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_10 : reg n3 a0 = (M0 (rp2)).zeroExtend 32 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_10, show (rp2) + 0x0 = rp2 from BitVec.add_zero _, fR2 _ (in2.r0 (toNat_pos_of_ne hr2))]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m3]; exact w2_2c
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m3]; exact w2_30
  have w3_3c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m3]; exact w2_3c
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m3]; exact w2_40
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m3]; exact w2_48
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m3]; exact w2_4c
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m3]; exact w2_50
  have w3_54 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m3]; exact w2_54
  have w3_58 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m3]; exact w2_58
  have w3_5c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m3]; exact w2_5c
  have w3_60 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m3]; exact w2_60
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m3]; exact w2_64
  have w3_68 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m3]; exact w2_68
  have w3_6c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m3]; exact w2_6c
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m3]; exact w2_70
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m3]; exact w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m3]; exact w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m3]; exact w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m3]; exact w2_84
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m3]; exact w2_88
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m3]; exact w2_8c
  have w3_90 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m3]; exact w2_90
  have w3_94 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m3]; exact w2_94
  have w3_98 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m3]; exact w2_98
  have w3_9c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m3]; exact w2_9c
  have w3_a0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m3]; exact w2_a0
  have w3_a4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m3]; exact w2_a4
  have w3_150 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m3]; exact w2_150
  have w3_154 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m3]; exact w2_154
  have w3_158 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m3]; exact w2_158
  have w3_15c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m3]; exact w2_15c
  have w3_408 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = rp2 := by rw [m3]; exact w2_408
  have w3_40c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = rem2 := by rw [m3]; exact w2_40c
  clear w2_40c w2_408 w2_15c w2_158 w2_154 w2_150 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_74 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_48 w2_40 w2_3c w2_30 w2_2c g2_10 g2_27 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_11 g2_9 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x436
  obtain ⟨n4, c4, u4⟩ := s3.block svX2c436 E3.self svX2c436_end
    ⟨trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x438 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svX2c436 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_9 : reg n4 (9 : Fin 32) = tbp := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
  have g4_10 : reg n4 a0 = (M0 (rp2)).zeroExtend 32 := by
    rw [rb4, runBlock_reg _ _ _ a0 s3.zero (by decide), g3_10]
  have g4_18 : reg n4 (18 : Fin 32) = out := by
    rw [rb4, runBlock_reg _ _ _ (18 : Fin 32) s3.zero (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = dg := by
    rw [rb4, runBlock_reg _ _ _ (20 : Fin 32) s3.zero (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = rootp := by
    rw [rb4, runBlock_reg _ _ _ (21 : Fin 32) s3.zero (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = ll := by
    rw [rb4, runBlock_reg _ _ _ (22 : Fin 32) s3.zero (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = sgp := by
    rw [rb4, runBlock_reg _ _ _ (23 : Fin 32) s3.zero (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = kp := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = sgl := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_27 : reg n4 (27 : Fin 32) = tbl := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_11 : reg n4 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svX2c436, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_9, g3_10, g3_11, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m4]; exact w3_2c
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m4]; exact w3_30
  have w4_3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m4]; exact w3_3c
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m4]; exact w3_40
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m4]; exact w3_48
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m4]; exact w3_4c
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m4]; exact w3_50
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m4]; exact w3_54
  have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m4]; exact w3_58
  have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m4]; exact w3_5c
  have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m4]; exact w3_60
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m4]; exact w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m4]; exact w3_68
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m4]; exact w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m4]; exact w3_70
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m4]; exact w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m4]; exact w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m4]; exact w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m4]; exact w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m4]; exact w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m4]; exact w3_8c
  have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m4]; exact w3_90
  have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m4]; exact w3_94
  have w4_98 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m4]; exact w3_98
  have w4_9c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m4]; exact w3_9c
  have w4_a0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m4]; exact w3_a0
  have w4_a4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m4]; exact w3_a4
  have w4_150 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m4]; exact w3_150
  have w4_154 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m4]; exact w3_154
  have w4_158 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m4]; exact w3_158
  have w4_15c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m4]; exact w3_15c
  have w4_408 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = rp2 := by rw [m4]; exact w3_408
  have w4_40c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = rem2 := by rw [m4]; exact w3_40c
  clear w3_40c w3_408 w3_15c w3_158 w3_154 w3_150 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_40 w3_3c w3_30 w3_2c g3_10 g3_27 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_11 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x438: branch, not taken
  obtain ⟨n5, d5, u5⟩ := s4.notTaken E4.self 0x43C sv_at_438
    (by decide) (by rw [g4_10, g4_11]; exact br_bne_byte_f (by decide) hb1)
  have s5 : St n5.mem SV n5 0x43C (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
  have g5_9 : reg n5 (9 : Fin 32) = tbp := by rw [u5.regs, g4_9]
  have g5_10 : reg n5 a0 = (M0 (rp2)).zeroExtend 32 := by rw [u5.regs, g4_10]
  have g5_11 : reg n5 a1 = BitVec.ofNat 32 0x1 := by rw [u5.regs, g4_11]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = dg := by rw [u5.regs, g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = rootp := by rw [u5.regs, g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = ll := by rw [u5.regs, g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = sgp := by rw [u5.regs, g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = kp := by rw [u5.regs, g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = sgl := by rw [u5.regs, g4_25]
  have g5_27 : reg n5 (27 : Fin 32) = tbl := by rw [u5.regs, g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m5]; exact w4_2c
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m5]; exact w4_30
  have w5_3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m5]; exact w4_3c
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m5]; exact w4_40
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m5]; exact w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m5]; exact w4_4c
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m5]; exact w4_50
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m5]; exact w4_54
  have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m5]; exact w4_58
  have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m5]; exact w4_5c
  have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m5]; exact w4_60
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m5]; exact w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m5]; exact w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m5]; exact w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m5]; exact w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m5]; exact w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m5]; exact w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m5]; exact w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m5]; exact w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m5]; exact w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m5]; exact w4_8c
  have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m5]; exact w4_90
  have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m5]; exact w4_94
  have w5_98 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m5]; exact w4_98
  have w5_9c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m5]; exact w4_9c
  have w5_a0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m5]; exact w4_a0
  have w5_a4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m5]; exact w4_a4
  have w5_150 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m5]; exact w4_150
  have w5_154 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m5]; exact w4_154
  have w5_158 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m5]; exact w4_158
  have w5_15c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m5]; exact w4_15c
  have w5_408 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = rp2 := by rw [m5]; exact w4_408
  have w5_40c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = rem2 := by rw [m5]; exact w4_40c
  clear w4_40c w4_408 w4_15c w4_158 w4_154 w4_150 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_40 w4_3c w4_30 w4_2c g4_11 g4_27 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x43C
  obtain ⟨n6, c6, u6⟩ := s5.block svX2c43c E5.self svX2c43c_end
    ⟨trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x440 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svX2c43c (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by
    rw [rb6, runBlock_reg _ _ _ sp s5.zero (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb6, runBlock_reg _ _ _ (3 : Fin 32) s5.zero (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb6, runBlock_reg _ _ _ (4 : Fin 32) s5.zero (by decide), g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = tbp := by
    rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
  have g6_11 : reg n6 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb6, runBlock_reg _ _ _ a1 s5.zero (by decide), g5_11]
  have g6_18 : reg n6 (18 : Fin 32) = out := by
    rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = dg := by
    rw [rb6, runBlock_reg _ _ _ (20 : Fin 32) s5.zero (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = rootp := by
    rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = ll := by
    rw [rb6, runBlock_reg _ _ _ (22 : Fin 32) s5.zero (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = sgp := by
    rw [rb6, runBlock_reg _ _ _ (23 : Fin 32) s5.zero (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = kp := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = sgl := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_27 : reg n6 (27 : Fin 32) = tbl := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svX2c43c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_9, g5_10, g5_11, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m6]; exact w5_2c
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m6]; exact w5_30
  have w6_3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m6]; exact w5_3c
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m6]; exact w5_40
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m6]; exact w5_48
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m6]; exact w5_4c
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m6]; exact w5_50
  have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m6]; exact w5_54
  have w6_58 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m6]; exact w5_58
  have w6_5c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m6]; exact w5_5c
  have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m6]; exact w5_60
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m6]; exact w5_64
  have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m6]; exact w5_68
  have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m6]; exact w5_6c
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m6]; exact w5_70
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m6]; exact w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m6]; exact w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m6]; exact w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m6]; exact w5_84
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m6]; exact w5_88
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m6]; exact w5_8c
  have w6_90 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m6]; exact w5_90
  have w6_94 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m6]; exact w5_94
  have w6_98 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m6]; exact w5_98
  have w6_9c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m6]; exact w5_9c
  have w6_a0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m6]; exact w5_a0
  have w6_a4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m6]; exact w5_a4
  have w6_150 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m6]; exact w5_150
  have w6_154 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m6]; exact w5_154
  have w6_158 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m6]; exact w5_158
  have w6_15c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m6]; exact w5_15c
  have w6_408 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = rp2 := by rw [m6]; exact w5_408
  have w6_40c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = rem2 := by rw [m6]; exact w5_40c
  clear w5_40c w5_408 w5_15c w5_158 w5_154 w5_150 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_40 w5_3c w5_30 w5_2c g5_27 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_11 g5_10 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x440: sv_boolF
  obtain ⟨n7, c7, s7, sp7, rk7, a0_7, K7, A7, fr7⟩ := sv_boolF (dc := 0x400)
    F E6 s6 sv_at_440 sv_at_444 (by decide) (by decide) g6_2 g6_10
    (by decide) (by decide) w6_408 w6_40c in2
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keepL K7 (by decide)
  rw [sv_mb fR6 in2] at a0_7 A7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rk7 sp (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk7 (3 : Fin 32) (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk7 (4 : Fin 32) (by decide) (by decide), g6_4]
  have g7_9 : reg n7 (9 : Fin 32) = tbp := by rw [rk7 (9 : Fin 32) (by decide) (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rk7 (18 : Fin 32) (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rk7 (19 : Fin 32) (by decide) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = dg := by rw [rk7 (20 : Fin 32) (by decide) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = rootp := by rw [rk7 (21 : Fin 32) (by decide) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = ll := by rw [rk7 (22 : Fin 32) (by decide) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = sgp := by rw [rk7 (23 : Fin 32) (by decide) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = kp := by rw [rk7 (24 : Fin 32) (by decide) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = sgl := by rw [rk7 (25 : Fin 32) (by decide) (by decide), g6_25]
  have g7_27 : reg n7 (27 : Fin 32) = tbl := by rw [rk7 (27 : Fin 32) (by decide) (by decide), g6_27]
  obtain ⟨r7, hr7⟩ : ∃ r, derBoolOf (memBytes M0 (rp2) (rem2).toNat) (derElement 1 (memBytes M0 (rp2) (rem2).toNat)) = r := ⟨_, rfl⟩
  rcases r7 with eb7 | ⟨⟩
  · have g7_10 : reg n7 a0 = (derErrByte eb7).zeroExtend 32 := by rw [a0_7, hr7]; rfl
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x408, 0x8)] := keep_kk6.trans K7
    clear keep_kk6
    have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K7.w32 (by decide) (by decide)).trans w6_2c
    have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K7.w32 (by decide) (by decide)).trans w6_30
    have w7_3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K7.w32 (by decide) (by decide)).trans w6_3c
    have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K7.w32 (by decide) (by decide)).trans w6_40
    have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K7.w32 (by decide) (by decide)).trans w6_48
    have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K7.w32 (by decide) (by decide)).trans w6_4c
    have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K7.w32 (by decide) (by decide)).trans w6_50
    have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K7.w32 (by decide) (by decide)).trans w6_54
    have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K7.w32 (by decide) (by decide)).trans w6_58
    have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K7.w32 (by decide) (by decide)).trans w6_5c
    have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K7.w32 (by decide) (by decide)).trans w6_60
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K7.w32 (by decide) (by decide)).trans w6_64
    have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K7.w32 (by decide) (by decide)).trans w6_68
    have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K7.w32 (by decide) (by decide)).trans w6_6c
    have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K7.w32 (by decide) (by decide)).trans w6_70
    have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K7.w32 (by decide) (by decide)).trans w6_74
    have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K7.w32 (by decide) (by decide)).trans w6_78
    have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K7.w32 (by decide) (by decide)).trans w6_7c
    have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K7.w32 (by decide) (by decide)).trans w6_80
    have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K7.w32 (by decide) (by decide)).trans w6_84
    have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K7.w32 (by decide) (by decide)).trans w6_88
    have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K7.w32 (by decide) (by decide)).trans w6_8c
    have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K7.w32 (by decide) (by decide)).trans w6_90
    have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K7.w32 (by decide) (by decide)).trans w6_94
    have w7_98 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K7.w32 (by decide) (by decide)).trans w6_98
    have w7_9c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K7.w32 (by decide) (by decide)).trans w6_9c
    have w7_a0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K7.w32 (by decide) (by decide)).trans w6_a0
    have w7_a4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K7.w32 (by decide) (by decide)).trans w6_a4
    have w7_150 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K7.w32 (by decide) (by decide)).trans w6_150
    have w7_154 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K7.w32 (by decide) (by decide)).trans w6_154
    have w7_158 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K7.w32 (by decide) (by decide)).trans w6_158
    have w7_15c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K7.w32 (by decide) (by decide)).trans w6_15c
    clear w6_40c w6_408 w6_15c w6_158 w6_154 w6_150 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_40 w6_3c w6_30 w6_2c g6_10 g6_27 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
    -- 0x448: sw
    obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_448 (off' := 0x44A) (c := 0x44)
      (by decide) (by rw [g7_2]; sv_addr) (by decide) (by decide)
    have t8 : Steps n0 n8 := t7.trans d8
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
    have g8_9 : reg n8 (9 : Fin 32) = tbp := by rw [rg8 (9 : Fin 32), g7_9]
    have g8_10 : reg n8 a0 = (derErrByte eb7).zeroExtend 32 := by rw [rg8 a0, g7_10]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [rg8 (20 : Fin 32), g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [rg8 (21 : Fin 32), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [rg8 (22 : Fin 32), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = sgp := by rw [rg8 (23 : Fin 32), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = kp := by rw [rg8 (24 : Fin 32), g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = sgl := by rw [rg8 (25 : Fin 32), g7_25]
    have g8_27 : reg n8 (27 : Fin 32) = tbl := by rw [rg8 (27 : Fin 32), g7_27]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x408, 0x8), (0x44, 0x4)] := keep_kk7.trans K8.toL
    clear keep_kk7
    have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K8.w32 (by decide) (by decide)).trans w7_2c
    have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K8.w32 (by decide) (by decide)).trans w7_30
    have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K8.w32 (by decide) (by decide)).trans w7_3c
    have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K8.w32 (by decide) (by decide)).trans w7_40
    have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K8.w32 (by decide) (by decide)).trans w7_48
    have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K8.w32 (by decide) (by decide)).trans w7_4c
    have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K8.w32 (by decide) (by decide)).trans w7_50
    have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K8.w32 (by decide) (by decide)).trans w7_54
    have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K8.w32 (by decide) (by decide)).trans w7_58
    have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K8.w32 (by decide) (by decide)).trans w7_5c
    have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K8.w32 (by decide) (by decide)).trans w7_60
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K8.w32 (by decide) (by decide)).trans w7_64
    have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K8.w32 (by decide) (by decide)).trans w7_68
    have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K8.w32 (by decide) (by decide)).trans w7_6c
    have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K8.w32 (by decide) (by decide)).trans w7_70
    have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K8.w32 (by decide) (by decide)).trans w7_74
    have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K8.w32 (by decide) (by decide)).trans w7_78
    have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K8.w32 (by decide) (by decide)).trans w7_7c
    have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K8.w32 (by decide) (by decide)).trans w7_80
    have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K8.w32 (by decide) (by decide)).trans w7_84
    have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K8.w32 (by decide) (by decide)).trans w7_88
    have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K8.w32 (by decide) (by decide)).trans w7_8c
    have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K8.w32 (by decide) (by decide)).trans w7_90
    have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K8.w32 (by decide) (by decide)).trans w7_94
    have w8_98 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K8.w32 (by decide) (by decide)).trans w7_98
    have w8_9c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K8.w32 (by decide) (by decide)).trans w7_9c
    have w8_a0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K8.w32 (by decide) (by decide)).trans w7_a0
    have w8_a4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K8.w32 (by decide) (by decide)).trans w7_a4
    have w8_150 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K8.w32 (by decide) (by decide)).trans w7_150
    have w8_154 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K8.w32 (by decide) (by decide)).trans w7_154
    have w8_158 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K8.w32 (by decide) (by decide)).trans w7_158
    have w8_15c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K8.w32 (by decide) (by decide)).trans w7_15c
    have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte eb7).zeroExtend 32 := by rw [W8, g7_10]
    clear w7_15c w7_158 w7_154 w7_150 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_40 w7_3c w7_30 w7_2c g7_10
    -- 0x44A
    obtain ⟨n9, c9, u9⟩ := s8.block svX2c44a E8.self svX2c44a_end
      ⟨trivial, trivial, trivial⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have s9 : St n9.mem SV n9 0x452 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have rb9 : ∀ q, reg n9 q = (runBlock svX2c44a (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
    have g9_9 : reg n9 (9 : Fin 32) = tbp := by
      rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
    have g9_18 : reg n9 (18 : Fin 32) = out := by
      rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by
      rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = dg := by
      rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = rootp := by
      rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = ll := by
      rw [rb9, runBlock_reg _ _ _ (22 : Fin 32) s8.zero (by decide), g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = sgp := by
      rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = kp := by
      rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = sgl := by
      rw [rb9, runBlock_reg _ _ _ (25 : Fin 32) s8.zero (by decide), g8_25]
    have g9_27 : reg n9 (27 : Fin 32) = tbl := by
      rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
    have g9_10 : reg n9 a0 = (((derErrByte eb7).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) + BitVec.ofNat 32 0xFFFFFF01 := by
      rw [rb9]; simp +decide only [runBlock, BInstr.run, svX2c44a, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g8_2, g8_3, g8_4, g8_9, g8_10, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_27, s8.zero])
      all_goals (try simp only [BitVec.ofNat_eq_ofNat])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x408, 0x8), (0x44, 0x4)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m9]; exact w8_2c
    have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m9]; exact w8_30
    have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m9]; exact w8_3c
    have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m9]; exact w8_40
    have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte eb7).zeroExtend 32 := by rw [m9]; exact w8_44
    have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m9]; exact w8_48
    have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m9]; exact w8_4c
    have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m9]; exact w8_50
    have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m9]; exact w8_54
    have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m9]; exact w8_58
    have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m9]; exact w8_5c
    have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m9]; exact w8_60
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
    have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m9]; exact w8_68
    have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m9]; exact w8_6c
    have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m9]; exact w8_70
    have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m9]; exact w8_74
    have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m9]; exact w8_78
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m9]; exact w8_7c
    have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m9]; exact w8_80
    have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m9]; exact w8_84
    have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m9]; exact w8_88
    have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m9]; exact w8_8c
    have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m9]; exact w8_90
    have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m9]; exact w8_94
    have w9_98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m9]; exact w8_98
    have w9_9c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m9]; exact w8_9c
    have w9_a0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m9]; exact w8_a0
    have w9_a4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m9]; exact w8_a4
    have w9_150 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m9]; exact w8_150
    have w9_154 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m9]; exact w8_154
    have w9_158 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m9]; exact w8_158
    have w9_15c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m9]; exact w8_15c
    clear w8_44 w8_15c w8_158 w8_154 w8_150 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_40 w8_3c w8_30 w8_2c g8_27 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
    -- 0x452: branch, taken
    obtain ⟨n10, d10, u10⟩ := s9.taken E9.self 0x944 sv_at_452
      (by decide) (by rw [g9_10, s9.zero]; exact br_bne_t (derErr_ff_ne eb7))
    have s10 : St n10.mem SV n10 0x944 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
    have g10_9 : reg n10 (9 : Fin 32) = tbp := by rw [u10.regs, g9_9]
    have g10_10 : reg n10 a0 = (((derErrByte eb7).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) + BitVec.ofNat 32 0xFFFFFF01 := by rw [u10.regs, g9_10]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = dg := by rw [u10.regs, g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = rootp := by rw [u10.regs, g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = ll := by rw [u10.regs, g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = sgp := by rw [u10.regs, g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = kp := by rw [u10.regs, g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = sgl := by rw [u10.regs, g9_25]
    have g10_27 : reg n10 (27 : Fin 32) = tbl := by rw [u10.regs, g9_27]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x408, 0x8), (0x44, 0x4)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m10]; exact w9_2c
    have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m10]; exact w9_30
    have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m10]; exact w9_3c
    have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m10]; exact w9_40
    have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte eb7).zeroExtend 32 := by rw [m10]; exact w9_44
    have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m10]; exact w9_48
    have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m10]; exact w9_4c
    have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m10]; exact w9_50
    have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m10]; exact w9_54
    have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m10]; exact w9_58
    have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m10]; exact w9_5c
    have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m10]; exact w9_60
    have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
    have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m10]; exact w9_68
    have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m10]; exact w9_6c
    have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m10]; exact w9_70
    have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
    have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m10]; exact w9_78
    have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m10]; exact w9_7c
    have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m10]; exact w9_80
    have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m10]; exact w9_84
    have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m10]; exact w9_88
    have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m10]; exact w9_8c
    have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m10]; exact w9_90
    have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m10]; exact w9_94
    have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m10]; exact w9_98
    have w10_9c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m10]; exact w9_9c
    have w10_a0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m10]; exact w9_a0
    have w10_a4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m10]; exact w9_a4
    have w10_150 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m10]; exact w9_150
    have w10_154 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m10]; exact w9_154
    have w10_158 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m10]; exact w9_158
    have w10_15c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m10]; exact w9_15c
    clear w9_15c w9_158 w9_154 w9_150 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_44 w9_40 w9_3c w9_30 w9_2c g9_10 g9_27 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
    -- 0x944: lw
    obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g10_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s11 : St n11.mem SV n11 0x946 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
    have g11_9 : reg n11 (9 : Fin 32) = tbp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
    have g11_10 : reg n11 a0 = (((derErrByte eb7).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) + BitVec.ofNat 32 0xFFFFFF01 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = sgp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = kp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = sgl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
    have g11_27 : reg n11 (27 : Fin 32) = tbl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x408, 0x8), (0x44, 0x4)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m11]; exact w10_2c
    have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m11]; exact w10_30
    have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m11]; exact w10_3c
    have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m11]; exact w10_40
    have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte eb7).zeroExtend 32 := by rw [m11]; exact w10_44
    have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m11]; exact w10_48
    have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m11]; exact w10_4c
    have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m11]; exact w10_50
    have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m11]; exact w10_54
    have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m11]; exact w10_58
    have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m11]; exact w10_5c
    have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m11]; exact w10_60
    have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
    have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m11]; exact w10_68
    have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m11]; exact w10_6c
    have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m11]; exact w10_70
    have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m11]; exact w10_74
    have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m11]; exact w10_78
    have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m11]; exact w10_7c
    have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m11]; exact w10_80
    have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m11]; exact w10_84
    have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m11]; exact w10_88
    have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m11]; exact w10_8c
    have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m11]; exact w10_90
    have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m11]; exact w10_94
    have w11_98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m11]; exact w10_98
    have w11_9c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m11]; exact w10_9c
    have w11_a0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m11]; exact w10_a0
    have w11_a4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m11]; exact w10_a4
    have w11_150 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m11]; exact w10_150
    have w11_154 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m11]; exact w10_154
    have w11_158 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m11]; exact w10_158
    have w11_15c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m11]; exact w10_15c
    clear w10_15c w10_158 w10_154 w10_150 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_40 w10_3c w10_30 w10_2c g10_27 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x946: j
    obtain ⟨n12, d12, u12⟩ := s11.jump E11.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s11.pc]; decide)
    have s12 : St n12.mem SV n12 0x7A4 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
    have g12_9 : reg n12 (9 : Fin 32) = tbp := by rw [u12.regs, g11_9]
    have g12_10 : reg n12 a0 = (((derErrByte eb7).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) + BitVec.ofNat 32 0xFFFFFF01 := by rw [u12.regs, g11_10]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = dg := by rw [u12.regs, g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = rootp := by rw [u12.regs, g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = ll := by rw [u12.regs, g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = sgp := by rw [u12.regs, g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = kp := by rw [u12.regs, g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = sgl := by rw [u12.regs, g11_25]
    have g12_27 : reg n12 (27 : Fin 32) = tbl := by rw [u12.regs, g11_27]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x408, 0x8), (0x44, 0x4)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m12]; exact w11_2c
    have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m12]; exact w11_30
    have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m12]; exact w11_3c
    have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m12]; exact w11_40
    have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte eb7).zeroExtend 32 := by rw [m12]; exact w11_44
    have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m12]; exact w11_48
    have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m12]; exact w11_4c
    have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m12]; exact w11_50
    have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m12]; exact w11_54
    have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m12]; exact w11_58
    have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m12]; exact w11_5c
    have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m12]; exact w11_60
    have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
    have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m12]; exact w11_68
    have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m12]; exact w11_6c
    have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m12]; exact w11_70
    have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m12]; exact w11_74
    have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m12]; exact w11_78
    have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m12]; exact w11_7c
    have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m12]; exact w11_80
    have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m12]; exact w11_84
    have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m12]; exact w11_88
    have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m12]; exact w11_8c
    have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m12]; exact w11_90
    have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m12]; exact w11_94
    have w12_98 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m12]; exact w11_98
    have w12_9c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m12]; exact w11_9c
    have w12_a0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m12]; exact w11_a0
    have w12_a4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m12]; exact w11_a4
    have w12_150 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m12]; exact w11_150
    have w12_154 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m12]; exact w11_154
    have w12_158 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m12]; exact w11_158
    have w12_15c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m12]; exact w11_15c
    clear w11_15c w11_158 w11_154 w11_150 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_3c w11_30 w11_2c g11_27 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    exact .inl ⟨(fun ⟨h0', _⟩ => by rw [hr7] at h0'; cases h0'), sv_fail F E12 s12 t12 (fun x hx => (fR12 x hx).trans (fM x hx).symm) V12 hret g12_2 g12_18 hO g12_3 g12_4⟩
  have g7_10 : reg n7 a0 = BitVec.ofNat 32 0xFFFFFFFF := by rw [a0_7, hr7]; rfl
  obtain ⟨tb7, htb7⟩ := bool_ok_elem hr7
  obtain ⟨d8_7, d12_7⟩ := A7 tb7 htb7
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x408, 0x8)] := keep_kk6.trans K7
  clear keep_kk6
  have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K7.w32 (by decide) (by decide)).trans w6_2c
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K7.w32 (by decide) (by decide)).trans w6_30
  have w7_3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K7.w32 (by decide) (by decide)).trans w6_3c
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K7.w32 (by decide) (by decide)).trans w6_40
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K7.w32 (by decide) (by decide)).trans w6_48
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K7.w32 (by decide) (by decide)).trans w6_4c
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K7.w32 (by decide) (by decide)).trans w6_50
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K7.w32 (by decide) (by decide)).trans w6_54
  have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K7.w32 (by decide) (by decide)).trans w6_58
  have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K7.w32 (by decide) (by decide)).trans w6_5c
  have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K7.w32 (by decide) (by decide)).trans w6_60
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K7.w32 (by decide) (by decide)).trans w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K7.w32 (by decide) (by decide)).trans w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K7.w32 (by decide) (by decide)).trans w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K7.w32 (by decide) (by decide)).trans w6_70
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K7.w32 (by decide) (by decide)).trans w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K7.w32 (by decide) (by decide)).trans w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K7.w32 (by decide) (by decide)).trans w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K7.w32 (by decide) (by decide)).trans w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K7.w32 (by decide) (by decide)).trans w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K7.w32 (by decide) (by decide)).trans w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K7.w32 (by decide) (by decide)).trans w6_8c
  have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K7.w32 (by decide) (by decide)).trans w6_90
  have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K7.w32 (by decide) (by decide)).trans w6_94
  have w7_98 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K7.w32 (by decide) (by decide)).trans w6_98
  have w7_9c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K7.w32 (by decide) (by decide)).trans w6_9c
  have w7_a0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K7.w32 (by decide) (by decide)).trans w6_a0
  have w7_a4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K7.w32 (by decide) (by decide)).trans w6_a4
  have w7_150 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K7.w32 (by decide) (by decide)).trans w6_150
  have w7_154 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K7.w32 (by decide) (by decide)).trans w6_154
  have w7_158 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K7.w32 (by decide) (by decide)).trans w6_158
  have w7_15c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K7.w32 (by decide) (by decide)).trans w6_15c
  have w7_408 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (rp2) + BitVec.ofNat 32 (tb7.header + tb7.len) := d8_7
  have w7_40c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (rem2) - BitVec.ofNat 32 (tb7.header + tb7.len) := d12_7
  clear w6_40c w6_408 w6_15c w6_158 w6_154 w6_150 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_40 w6_3c w6_30 w6_2c g6_10 g6_27 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0x448: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_448 (off' := 0x44A) (c := 0x44)
    (by decide) (by rw [g7_2]; sv_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_9 : reg n8 (9 : Fin 32) = tbp := by rw [rg8 (9 : Fin 32), g7_9]
  have g8_10 : reg n8 a0 = BitVec.ofNat 32 0xFFFFFFFF := by rw [rg8 a0, g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [rg8 (20 : Fin 32), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [rg8 (22 : Fin 32), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = sgp := by rw [rg8 (23 : Fin 32), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = kp := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = sgl := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_27 : reg n8 (27 : Fin 32) = tbl := by rw [rg8 (27 : Fin 32), g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x408, 0x8), (0x44, 0x4)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K8.w32 (by decide) (by decide)).trans w7_2c
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K8.w32 (by decide) (by decide)).trans w7_30
  have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K8.w32 (by decide) (by decide)).trans w7_3c
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K8.w32 (by decide) (by decide)).trans w7_40
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K8.w32 (by decide) (by decide)).trans w7_48
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K8.w32 (by decide) (by decide)).trans w7_4c
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K8.w32 (by decide) (by decide)).trans w7_50
  have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K8.w32 (by decide) (by decide)).trans w7_54
  have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K8.w32 (by decide) (by decide)).trans w7_58
  have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K8.w32 (by decide) (by decide)).trans w7_5c
  have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K8.w32 (by decide) (by decide)).trans w7_60
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K8.w32 (by decide) (by decide)).trans w7_64
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K8.w32 (by decide) (by decide)).trans w7_68
  have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K8.w32 (by decide) (by decide)).trans w7_6c
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K8.w32 (by decide) (by decide)).trans w7_70
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K8.w32 (by decide) (by decide)).trans w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K8.w32 (by decide) (by decide)).trans w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K8.w32 (by decide) (by decide)).trans w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K8.w32 (by decide) (by decide)).trans w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K8.w32 (by decide) (by decide)).trans w7_84
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K8.w32 (by decide) (by decide)).trans w7_88
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K8.w32 (by decide) (by decide)).trans w7_8c
  have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K8.w32 (by decide) (by decide)).trans w7_90
  have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K8.w32 (by decide) (by decide)).trans w7_94
  have w8_98 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K8.w32 (by decide) (by decide)).trans w7_98
  have w8_9c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K8.w32 (by decide) (by decide)).trans w7_9c
  have w8_a0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K8.w32 (by decide) (by decide)).trans w7_a0
  have w8_a4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K8.w32 (by decide) (by decide)).trans w7_a4
  have w8_150 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K8.w32 (by decide) (by decide)).trans w7_150
  have w8_154 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K8.w32 (by decide) (by decide)).trans w7_154
  have w8_158 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K8.w32 (by decide) (by decide)).trans w7_158
  have w8_15c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K8.w32 (by decide) (by decide)).trans w7_15c
  have w8_408 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (rp2) + BitVec.ofNat 32 (tb7.header + tb7.len) := (K8.w32 (by decide) (by decide)).trans w7_408
  have w8_40c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (rem2) - BitVec.ofNat 32 (tb7.header + tb7.len) := (K8.w32 (by decide) (by decide)).trans w7_40c
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [W8, g7_10]
  clear w7_40c w7_408 w7_15c w7_158 w7_154 w7_150 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_40 w7_3c w7_30 w7_2c d12_7 d8_7 g7_10 g7_27 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 A7 K7 a0_7 rk7 sp7 s7 c7
  -- 0x44A
  obtain ⟨n9, c9, u9⟩ := s8.block svX2c44a E8.self svX2c44a_end
    ⟨trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0x452 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svX2c44a (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_9 : reg n9 (9 : Fin 32) = tbp := by
    rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = dg := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = rootp := by
    rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = ll := by
    rw [rb9, runBlock_reg _ _ _ (22 : Fin 32) s8.zero (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = sgp := by
    rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = kp := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = sgl := by
    rw [rb9, runBlock_reg _ _ _ (25 : Fin 32) s8.zero (by decide), g8_25]
  have g9_27 : reg n9 (27 : Fin 32) = tbl := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_10 : reg n9 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svX2c44a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_9, g8_10, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x408, 0x8), (0x44, 0x4)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m9]; exact w8_2c
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m9]; exact w8_30
  have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m9]; exact w8_3c
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m9]; exact w8_40
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m9]; exact w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m9]; exact w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m9]; exact w8_4c
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m9]; exact w8_50
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m9]; exact w8_54
  have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m9]; exact w8_58
  have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m9]; exact w8_5c
  have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m9]; exact w8_60
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m9]; exact w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m9]; exact w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m9]; exact w8_70
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m9]; exact w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m9]; exact w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m9]; exact w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m9]; exact w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m9]; exact w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m9]; exact w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m9]; exact w8_8c
  have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m9]; exact w8_90
  have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m9]; exact w8_94
  have w9_98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m9]; exact w8_98
  have w9_9c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m9]; exact w8_9c
  have w9_a0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m9]; exact w8_a0
  have w9_a4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m9]; exact w8_a4
  have w9_150 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m9]; exact w8_150
  have w9_154 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m9]; exact w8_154
  have w9_158 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m9]; exact w8_158
  have w9_15c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m9]; exact w8_15c
  have w9_408 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (rp2) + BitVec.ofNat 32 (tb7.header + tb7.len) := by rw [m9]; exact w8_408
  have w9_40c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (rem2) - BitVec.ofNat 32 (tb7.header + tb7.len) := by rw [m9]; exact w8_40c
  clear w8_44 w8_40c w8_408 w8_15c w8_158 w8_154 w8_150 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_40 w8_3c w8_30 w8_2c g8_27 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0x452: branch, not taken
  obtain ⟨n10, d10, u10⟩ := s9.notTaken E9.self 0x456 sv_at_452
    (by decide) (by rw [g9_10, s9.zero]; decide)
  have s10 : St n10.mem SV n10 0x456 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
  have g10_9 : reg n10 (9 : Fin 32) = tbp := by rw [u10.regs, g9_9]
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 0x0 := by rw [u10.regs, g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = dg := by rw [u10.regs, g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = rootp := by rw [u10.regs, g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = ll := by rw [u10.regs, g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = sgp := by rw [u10.regs, g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = kp := by rw [u10.regs, g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = sgl := by rw [u10.regs, g9_25]
  have g10_27 : reg n10 (27 : Fin 32) = tbl := by rw [u10.regs, g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x408, 0x8), (0x44, 0x4)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m10]; exact w9_2c
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m10]; exact w9_30
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m10]; exact w9_3c
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m10]; exact w9_40
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m10]; exact w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m10]; exact w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m10]; exact w9_4c
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m10]; exact w9_50
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m10]; exact w9_54
  have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m10]; exact w9_58
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m10]; exact w9_5c
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m10]; exact w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m10]; exact w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m10]; exact w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m10]; exact w9_70
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m10]; exact w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m10]; exact w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m10]; exact w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m10]; exact w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m10]; exact w9_8c
  have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m10]; exact w9_90
  have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m10]; exact w9_94
  have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m10]; exact w9_98
  have w10_9c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m10]; exact w9_9c
  have w10_a0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m10]; exact w9_a0
  have w10_a4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m10]; exact w9_a4
  have w10_150 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m10]; exact w9_150
  have w10_154 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m10]; exact w9_154
  have w10_158 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m10]; exact w9_158
  have w10_15c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m10]; exact w9_15c
  have w10_408 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (rp2) + BitVec.ofNat 32 (tb7.header + tb7.len) := by rw [m10]; exact w9_408
  have w10_40c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (rem2) - BitVec.ofNat 32 (tb7.header + tb7.len) := by rw [m10]; exact w9_40c
  clear w9_40c w9_408 w9_15c w9_158 w9_154 w9_150 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_44 w9_40 w9_3c w9_30 w9_2c g9_10 g9_27 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x456
  obtain ⟨n11, c11, u11⟩ := s10.block svX2c456 E10.self svX2c456_end
    ⟨trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0x458 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svX2c456 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
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
  have g11_9 : reg n11 (9 : Fin 32) = tbp := by
    rw [rb11, runBlock_reg _ _ _ (9 : Fin 32) s10.zero (by decide), g10_9]
  have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb11, runBlock_reg _ _ _ a0 s10.zero (by decide), g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = dg := by
    rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = rootp := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = ll := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = sgp := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = kp := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = sgl := by
    rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
  have g11_27 : reg n11 (27 : Fin 32) = tbl := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_26 : reg n11 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svX2c456, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_9, g10_10, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_25, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x408, 0x8), (0x44, 0x4)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m11]; exact w10_2c
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m11]; exact w10_30
  have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m11]; exact w10_3c
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m11]; exact w10_40
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m11]; exact w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m11]; exact w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m11]; exact w10_4c
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m11]; exact w10_50
  have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m11]; exact w10_54
  have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m11]; exact w10_58
  have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m11]; exact w10_5c
  have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m11]; exact w10_60
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m11]; exact w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m11]; exact w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m11]; exact w10_70
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m11]; exact w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m11]; exact w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m11]; exact w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m11]; exact w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m11]; exact w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m11]; exact w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m11]; exact w10_8c
  have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m11]; exact w10_90
  have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m11]; exact w10_94
  have w11_98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m11]; exact w10_98
  have w11_9c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m11]; exact w10_9c
  have w11_a0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m11]; exact w10_a0
  have w11_a4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m11]; exact w10_a4
  have w11_150 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m11]; exact w10_150
  have w11_154 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m11]; exact w10_154
  have w11_158 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m11]; exact w10_158
  have w11_15c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m11]; exact w10_15c
  have w11_408 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (rp2) + BitVec.ofNat 32 (tb7.header + tb7.len) := by rw [m11]; exact w10_408
  have w11_40c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (rem2) - BitVec.ofNat 32 (tb7.header + tb7.len) := by rw [m11]; exact w10_40c
  clear w10_40c w10_408 w10_15c w10_158 w10_154 w10_150 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_40 w10_3c w10_30 w10_2c g10_27 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x458: j
  obtain ⟨n12, d12, u12⟩ := s11.jump E11.self sv_at_458 (off' := 0x45C) (by decide)
    (by rw [s11.pc]; decide)
  have s12 : St n12.mem SV n12 0x45C (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
  have g12_9 : reg n12 (9 : Fin 32) = tbp := by rw [u12.regs, g11_9]
  have g12_10 : reg n12 a0 = BitVec.ofNat 32 0x0 := by rw [u12.regs, g11_10]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = dg := by rw [u12.regs, g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = rootp := by rw [u12.regs, g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = ll := by rw [u12.regs, g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = sgp := by rw [u12.regs, g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = kp := by rw [u12.regs, g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = sgl := by rw [u12.regs, g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u12.regs, g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = tbl := by rw [u12.regs, g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x408, 0x8), (0x44, 0x4)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m12]; exact w11_2c
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m12]; exact w11_30
  have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m12]; exact w11_3c
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m12]; exact w11_40
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m12]; exact w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m12]; exact w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m12]; exact w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m12]; exact w11_50
  have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m12]; exact w11_54
  have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m12]; exact w11_58
  have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m12]; exact w11_5c
  have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m12]; exact w11_60
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m12]; exact w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m12]; exact w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m12]; exact w11_70
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m12]; exact w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m12]; exact w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m12]; exact w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m12]; exact w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m12]; exact w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m12]; exact w11_8c
  have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m12]; exact w11_90
  have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m12]; exact w11_94
  have w12_98 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m12]; exact w11_98
  have w12_9c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m12]; exact w11_9c
  have w12_a0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m12]; exact w11_a0
  have w12_a4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m12]; exact w11_a4
  have w12_150 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m12]; exact w11_150
  have w12_154 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m12]; exact w11_154
  have w12_158 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m12]; exact w11_158
  have w12_15c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m12]; exact w11_15c
  have w12_408 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (rp2) + BitVec.ofNat 32 (tb7.header + tb7.len) := by rw [m12]; exact w11_408
  have w12_40c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (rem2) - BitVec.ofNat 32 (tb7.header + tb7.len) := by rw [m12]; exact w11_40c
  clear w11_40c w11_408 w11_15c w11_158 w11_154 w11_150 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_3c w11_30 w11_2c g11_26 g11_27 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0x45C
  obtain ⟨n13, c13, u13⟩ := s12.block svX2c45c E12.self svX2c45c_end
    ⟨trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x464 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svX2c45c (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_9 : reg n13 (9 : Fin 32) = tbp := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = dg := by
    rw [rb13, runBlock_reg _ _ _ (20 : Fin 32) s12.zero (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = rootp := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = ll := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = sgp := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = kp := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = sgl := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = tbl := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svX2c45c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_9, g12_10, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g13_11 : reg n13 a1 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svX2c45c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_9, g12_10, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x408, 0x8), (0x44, 0x4)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m13]; exact w12_2c
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m13]; exact w12_30
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m13]; exact w12_3c
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m13]; exact w12_40
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m13]; exact w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m13]; exact w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m13]; exact w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m13]; exact w12_50
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m13]; exact w12_54
  have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m13]; exact w12_58
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m13]; exact w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m13]; exact w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m13]; exact w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m13]; exact w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m13]; exact w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m13]; exact w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m13]; exact w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m13]; exact w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m13]; exact w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m13]; exact w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m13]; exact w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m13]; exact w12_8c
  have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m13]; exact w12_90
  have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m13]; exact w12_94
  have w13_98 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m13]; exact w12_98
  have w13_9c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m13]; exact w12_9c
  have w13_a0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m13]; exact w12_a0
  have w13_a4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m13]; exact w12_a4
  have w13_150 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m13]; exact w12_150
  have w13_154 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m13]; exact w12_154
  have w13_158 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m13]; exact w12_158
  have w13_15c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m13]; exact w12_15c
  have w13_408 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (rp2) + BitVec.ofNat 32 (tb7.header + tb7.len) := by rw [m13]; exact w12_408
  have w13_40c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (rem2) - BitVec.ofNat 32 (tb7.header + tb7.len) := by rw [m13]; exact w12_40c
  clear w12_40c w12_408 w12_15c w12_158 w12_154 w12_150 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_44 w12_40 w12_3c w12_30 w12_2c g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x464: sv_octF
  obtain ⟨n14, c14, s14, sp14, rk14, K14, A14, Ok14, Er14, fr14⟩ := sv_octF (oc := 0x420) (dc := 0x400)
    F E13 s13 sv_at_464 sv_at_468 (by decide) (by decide) g13_2 g13_10 g13_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w13_408 w13_40c (in2.restW htb7)
  have t14 : Steps n0 n14 := t13.trans c14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keepL K14 (by decide)
  rw [sv_mb fR13 (in2.restW htb7)] at A14 Ok14 Er14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rk14 sp (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk14 (3 : Fin 32) (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk14 (4 : Fin 32) (by decide) (by decide), g13_4]
  have g14_9 : reg n14 (9 : Fin 32) = tbp := by rw [rk14 (9 : Fin 32) (by decide) (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rk14 (18 : Fin 32) (by decide) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rk14 (19 : Fin 32) (by decide) (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = dg := by rw [rk14 (20 : Fin 32) (by decide) (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = rootp := by rw [rk14 (21 : Fin 32) (by decide) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = ll := by rw [rk14 (22 : Fin 32) (by decide) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = sgp := by rw [rk14 (23 : Fin 32) (by decide) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = kp := by rw [rk14 (24 : Fin 32) (by decide) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = sgl := by rw [rk14 (25 : Fin 32) (by decide) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk14 (26 : Fin 32) (by decide) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = tbl := by rw [rk14 (27 : Fin 32) (by decide) (by decide), g13_27]
  obtain ⟨r14, hr14⟩ : ∃ r, derContent ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) (derElement 4 (memBytes M0 ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)).toNat)) = r := ⟨_, rfl⟩
  rcases r14 with er14 | ⟨vp14, vl14⟩
  · obtain ⟨z14, -⟩ := Er14 er14 hr14
    have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8)] := keep_kk13.trans K14
    clear keep_kk13
    have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K14.w32 (by decide) (by decide)).trans w13_2c
    have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K14.w32 (by decide) (by decide)).trans w13_30
    have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K14.w32 (by decide) (by decide)).trans w13_3c
    have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K14.w32 (by decide) (by decide)).trans w13_40
    have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := (K14.w32 (by decide) (by decide)).trans w13_44
    have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K14.w32 (by decide) (by decide)).trans w13_48
    have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K14.w32 (by decide) (by decide)).trans w13_4c
    have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K14.w32 (by decide) (by decide)).trans w13_50
    have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K14.w32 (by decide) (by decide)).trans w13_54
    have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K14.w32 (by decide) (by decide)).trans w13_58
    have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K14.w32 (by decide) (by decide)).trans w13_5c
    have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K14.w32 (by decide) (by decide)).trans w13_60
    have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K14.w32 (by decide) (by decide)).trans w13_64
    have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K14.w32 (by decide) (by decide)).trans w13_68
    have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K14.w32 (by decide) (by decide)).trans w13_6c
    have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K14.w32 (by decide) (by decide)).trans w13_70
    have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K14.w32 (by decide) (by decide)).trans w13_74
    have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K14.w32 (by decide) (by decide)).trans w13_78
    have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K14.w32 (by decide) (by decide)).trans w13_7c
    have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K14.w32 (by decide) (by decide)).trans w13_80
    have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K14.w32 (by decide) (by decide)).trans w13_84
    have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K14.w32 (by decide) (by decide)).trans w13_88
    have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K14.w32 (by decide) (by decide)).trans w13_8c
    have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K14.w32 (by decide) (by decide)).trans w13_90
    have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K14.w32 (by decide) (by decide)).trans w13_94
    have w14_98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K14.w32 (by decide) (by decide)).trans w13_98
    have w14_9c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K14.w32 (by decide) (by decide)).trans w13_9c
    have w14_a0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K14.w32 (by decide) (by decide)).trans w13_a0
    have w14_a4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K14.w32 (by decide) (by decide)).trans w13_a4
    have w14_150 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K14.w32 (by decide) (by decide)).trans w13_150
    have w14_154 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K14.w32 (by decide) (by decide)).trans w13_154
    have w14_158 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K14.w32 (by decide) (by decide)).trans w13_158
    have w14_15c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K14.w32 (by decide) (by decide)).trans w13_15c
    have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z14
    clear w13_40c w13_408 w13_15c w13_158 w13_154 w13_150 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_44 w13_40 w13_3c w13_30 w13_2c g13_11 g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
    -- 0x46C: lw
    obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_46c (off' := 0x470) (by decide)
      (by rw [g14_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s15 : St n15.mem SV n15 0x470 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
    have t15 : Steps n0 n15 := t14.trans (.single d15)
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.same m15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
    have g15_9 : reg n15 (9 : Fin 32) = tbp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
    have g15_20 : reg n15 (20 : Fin 32) = dg := by rw [u15.regs, upd_ne (by decide) (by decide), g14_20]
    have g15_21 : reg n15 (21 : Fin 32) = rootp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = ll := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = sgp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = kp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = sgl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = tbl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
    have g15_10 : reg n15 a0 = 0 := by
      rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g14_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w14_420]
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8)] := by rw [m15]; exact keep_kk14
    clear keep_kk14
    have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m15]; exact w14_2c
    have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m15]; exact w14_30
    have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m15]; exact w14_3c
    have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m15]; exact w14_40
    have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m15]; exact w14_44
    have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m15]; exact w14_48
    have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m15]; exact w14_4c
    have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m15]; exact w14_50
    have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m15]; exact w14_54
    have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m15]; exact w14_58
    have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m15]; exact w14_5c
    have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m15]; exact w14_60
    have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
    have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m15]; exact w14_68
    have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m15]; exact w14_6c
    have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m15]; exact w14_70
    have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m15]; exact w14_74
    have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m15]; exact w14_78
    have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m15]; exact w14_7c
    have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m15]; exact w14_80
    have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m15]; exact w14_84
    have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m15]; exact w14_88
    have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m15]; exact w14_8c
    have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m15]; exact w14_90
    have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m15]; exact w14_94
    have w15_98 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m15]; exact w14_98
    have w15_9c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m15]; exact w14_9c
    have w15_a0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m15]; exact w14_a0
    have w15_a4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m15]; exact w14_a4
    have w15_150 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m15]; exact w14_150
    have w15_154 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m15]; exact w14_154
    have w15_158 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m15]; exact w14_158
    have w15_15c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m15]; exact w14_15c
    have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m15]; exact w14_420
    clear w14_420 w14_15c w14_158 w14_154 w14_150 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_30 w14_2c z14
    -- 0x470: sw
    obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_470 (off' := 0x472) (c := 0x38)
      (by decide) (by rw [g15_2]; sv_addr) (by decide) (by decide)
    have t16 : Steps n0 n16 := t15.trans d16
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
    have g16_9 : reg n16 (9 : Fin 32) = tbp := by rw [rg16 (9 : Fin 32), g15_9]
    have g16_10 : reg n16 a0 = 0 := by rw [rg16 a0, g15_10]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = dg := by rw [rg16 (20 : Fin 32), g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = rootp := by rw [rg16 (21 : Fin 32), g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = ll := by rw [rg16 (22 : Fin 32), g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = sgp := by rw [rg16 (23 : Fin 32), g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = kp := by rw [rg16 (24 : Fin 32), g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = sgl := by rw [rg16 (25 : Fin 32), g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg16 (26 : Fin 32), g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = tbl := by rw [rg16 (27 : Fin 32), g15_27]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4)] := keep_kk15.trans K16.toL
    clear keep_kk15
    have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K16.w32 (by decide) (by decide)).trans w15_2c
    have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K16.w32 (by decide) (by decide)).trans w15_30
    have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K16.w32 (by decide) (by decide)).trans w15_3c
    have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K16.w32 (by decide) (by decide)).trans w15_40
    have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := (K16.w32 (by decide) (by decide)).trans w15_44
    have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K16.w32 (by decide) (by decide)).trans w15_48
    have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K16.w32 (by decide) (by decide)).trans w15_4c
    have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K16.w32 (by decide) (by decide)).trans w15_50
    have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K16.w32 (by decide) (by decide)).trans w15_54
    have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K16.w32 (by decide) (by decide)).trans w15_58
    have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K16.w32 (by decide) (by decide)).trans w15_5c
    have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K16.w32 (by decide) (by decide)).trans w15_60
    have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K16.w32 (by decide) (by decide)).trans w15_64
    have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K16.w32 (by decide) (by decide)).trans w15_68
    have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K16.w32 (by decide) (by decide)).trans w15_6c
    have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K16.w32 (by decide) (by decide)).trans w15_70
    have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K16.w32 (by decide) (by decide)).trans w15_74
    have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K16.w32 (by decide) (by decide)).trans w15_78
    have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K16.w32 (by decide) (by decide)).trans w15_7c
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K16.w32 (by decide) (by decide)).trans w15_80
    have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K16.w32 (by decide) (by decide)).trans w15_84
    have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K16.w32 (by decide) (by decide)).trans w15_88
    have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K16.w32 (by decide) (by decide)).trans w15_8c
    have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K16.w32 (by decide) (by decide)).trans w15_90
    have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K16.w32 (by decide) (by decide)).trans w15_94
    have w16_98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K16.w32 (by decide) (by decide)).trans w15_98
    have w16_9c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K16.w32 (by decide) (by decide)).trans w15_9c
    have w16_a0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K16.w32 (by decide) (by decide)).trans w15_a0
    have w16_a4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K16.w32 (by decide) (by decide)).trans w15_a4
    have w16_150 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K16.w32 (by decide) (by decide)).trans w15_150
    have w16_154 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K16.w32 (by decide) (by decide)).trans w15_154
    have w16_158 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K16.w32 (by decide) (by decide)).trans w15_158
    have w16_15c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K16.w32 (by decide) (by decide)).trans w15_15c
    have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K16.w32 (by decide) (by decide)).trans w15_420
    have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = 0 := by rw [W16, g15_10]
    clear w15_420 w15_15c w15_158 w15_154 w15_150 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_30 w15_2c g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
    -- 0x472: branch, taken
    obtain ⟨n17, d17, u17⟩ := s16.taken E16.self 0x7F2 sv_at_472
      (by decide) (by rw [g16_10, s16.zero]; rfl)
    have s17 : St n17.mem SV n17 0x7F2 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
    have g17_9 : reg n17 (9 : Fin 32) = tbp := by rw [u17.regs, g16_9]
    have g17_10 : reg n17 a0 = 0 := by rw [u17.regs, g16_10]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [u17.regs, g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [u17.regs, g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [u17.regs, g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = sgp := by rw [u17.regs, g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = kp := by rw [u17.regs, g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = sgl := by rw [u17.regs, g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u17.regs, g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = tbl := by rw [u17.regs, g16_27]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m17]; exact w16_2c
    have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m17]; exact w16_30
    have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = 0 := by rw [m17]; exact w16_38
    have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m17]; exact w16_3c
    have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m17]; exact w16_40
    have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m17]; exact w16_44
    have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m17]; exact w16_48
    have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m17]; exact w16_4c
    have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m17]; exact w16_50
    have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m17]; exact w16_54
    have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m17]; exact w16_58
    have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m17]; exact w16_5c
    have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m17]; exact w16_60
    have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m17]; exact w16_64
    have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m17]; exact w16_68
    have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m17]; exact w16_6c
    have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m17]; exact w16_70
    have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m17]; exact w16_74
    have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m17]; exact w16_78
    have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m17]; exact w16_7c
    have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m17]; exact w16_80
    have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m17]; exact w16_84
    have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m17]; exact w16_88
    have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m17]; exact w16_8c
    have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m17]; exact w16_90
    have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m17]; exact w16_94
    have w17_98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m17]; exact w16_98
    have w17_9c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m17]; exact w16_9c
    have w17_a0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m17]; exact w16_a0
    have w17_a4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m17]; exact w16_a4
    have w17_150 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m17]; exact w16_150
    have w17_154 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m17]; exact w16_154
    have w17_158 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m17]; exact w16_158
    have w17_15c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m17]; exact w16_15c
    have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m17]; exact w16_420
    clear w16_38 w16_420 w16_15c w16_158 w16_154 w16_150 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_30 w16_2c g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_10 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
    -- 0x7F2: lbu
    obtain ⟨n18, d18, u18⟩ := s17.lbu E17.self sv_at_7f2 (off' := 0x7F6) (by decide)
    have s18 : St n18.mem SV n18 0x7F6 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
    have g18_9 : reg n18 (9 : Fin 32) = tbp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_9]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
    have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [u18.regs, upd_ne (by decide) (by decide), g17_20]
    have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = sgp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = kp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = sgl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = tbl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4)] := by rw [m18]; exact keep_kk17
    clear keep_kk17
    have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m18]; exact w17_2c
    have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m18]; exact w17_30
    have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = 0 := by rw [m18]; exact w17_38
    have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m18]; exact w17_3c
    have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m18]; exact w17_40
    have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m18]; exact w17_44
    have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m18]; exact w17_48
    have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m18]; exact w17_4c
    have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m18]; exact w17_50
    have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m18]; exact w17_54
    have w18_58 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m18]; exact w17_58
    have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m18]; exact w17_5c
    have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m18]; exact w17_60
    have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m18]; exact w17_64
    have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m18]; exact w17_68
    have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m18]; exact w17_6c
    have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m18]; exact w17_70
    have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m18]; exact w17_74
    have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m18]; exact w17_78
    have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m18]; exact w17_7c
    have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m18]; exact w17_80
    have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m18]; exact w17_84
    have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m18]; exact w17_88
    have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m18]; exact w17_8c
    have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m18]; exact w17_90
    have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m18]; exact w17_94
    have w18_98 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m18]; exact w17_98
    have w18_9c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m18]; exact w17_9c
    have w18_a0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m18]; exact w17_a0
    have w18_a4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m18]; exact w17_a4
    have w18_150 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m18]; exact w17_150
    have w18_154 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m18]; exact w17_154
    have w18_158 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m18]; exact w17_158
    have w18_15c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m18]; exact w17_15c
    have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m18]; exact w17_420
    clear w17_420 w17_15c w17_158 w17_154 w17_150 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_30 w17_2c g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_10 g17_9 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
    -- 0x7F6: j
    obtain ⟨n19, d19, u19⟩ := s18.jump E18.self sv_at_7f6 (off' := 0x942) (by decide)
      (by rw [s18.pc]; decide)
    have s19 : St n19.mem SV n19 0x942 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
    have g19_9 : reg n19 (9 : Fin 32) = tbp := by rw [u19.regs, g18_9]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = dg := by rw [u19.regs, g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = rootp := by rw [u19.regs, g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = ll := by rw [u19.regs, g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = sgp := by rw [u19.regs, g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = kp := by rw [u19.regs, g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = sgl := by rw [u19.regs, g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u19.regs, g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = tbl := by rw [u19.regs, g18_27]
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m19]; exact w18_2c
    have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m19]; exact w18_30
    have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = 0 := by rw [m19]; exact w18_38
    have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m19]; exact w18_3c
    have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m19]; exact w18_40
    have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m19]; exact w18_44
    have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m19]; exact w18_48
    have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m19]; exact w18_4c
    have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m19]; exact w18_50
    have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m19]; exact w18_54
    have w19_58 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m19]; exact w18_58
    have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m19]; exact w18_5c
    have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m19]; exact w18_60
    have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m19]; exact w18_64
    have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m19]; exact w18_68
    have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m19]; exact w18_6c
    have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m19]; exact w18_70
    have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m19]; exact w18_74
    have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m19]; exact w18_78
    have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m19]; exact w18_7c
    have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m19]; exact w18_80
    have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m19]; exact w18_84
    have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m19]; exact w18_88
    have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m19]; exact w18_8c
    have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m19]; exact w18_90
    have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m19]; exact w18_94
    have w19_98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m19]; exact w18_98
    have w19_9c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m19]; exact w18_9c
    have w19_a0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m19]; exact w18_a0
    have w19_a4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m19]; exact w18_a4
    have w19_150 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m19]; exact w18_150
    have w19_154 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m19]; exact w18_154
    have w19_158 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m19]; exact w18_158
    have w19_15c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m19]; exact w18_15c
    have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m19]; exact w18_420
    clear w18_420 w18_15c w18_158 w18_154 w18_150 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_30 w18_2c g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    -- 0x942: sw
    obtain ⟨n20, d20, s20, fr20, K20, W20, rg20⟩ := sv_sw F E19 s19 sv_at_942 (off' := 0x944) (c := 0x44)
      (by decide) (by rw [g19_2]; sv_addr) (by decide) (by decide)
    have t20 : Steps n0 n20 := t19.trans d20
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.keep K20 (by decide)
    have g20_2 : reg n20 sp = B + 0x21A0 := by rw [rg20 sp, g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg20 (3 : Fin 32), g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg20 (4 : Fin 32), g19_4]
    have g20_9 : reg n20 (9 : Fin 32) = tbp := by rw [rg20 (9 : Fin 32), g19_9]
    have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rg20 (18 : Fin 32), g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rg20 (19 : Fin 32), g19_19]
    have g20_20 : reg n20 (20 : Fin 32) = dg := by rw [rg20 (20 : Fin 32), g19_20]
    have g20_21 : reg n20 (21 : Fin 32) = rootp := by rw [rg20 (21 : Fin 32), g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = ll := by rw [rg20 (22 : Fin 32), g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = sgp := by rw [rg20 (23 : Fin 32), g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = kp := by rw [rg20 (24 : Fin 32), g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = sgl := by rw [rg20 (25 : Fin 32), g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg20 (26 : Fin 32), g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = tbl := by rw [rg20 (27 : Fin 32), g19_27]
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x44, 0x4)] := keep_kk19.trans K20.toL
    clear keep_kk19
    have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K20.w32 (by decide) (by decide)).trans w19_2c
    have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K20.w32 (by decide) (by decide)).trans w19_30
    have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = 0 := (K20.w32 (by decide) (by decide)).trans w19_38
    have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K20.w32 (by decide) (by decide)).trans w19_3c
    have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K20.w32 (by decide) (by decide)).trans w19_40
    have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K20.w32 (by decide) (by decide)).trans w19_48
    have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K20.w32 (by decide) (by decide)).trans w19_4c
    have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K20.w32 (by decide) (by decide)).trans w19_50
    have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K20.w32 (by decide) (by decide)).trans w19_54
    have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K20.w32 (by decide) (by decide)).trans w19_58
    have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K20.w32 (by decide) (by decide)).trans w19_5c
    have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K20.w32 (by decide) (by decide)).trans w19_60
    have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K20.w32 (by decide) (by decide)).trans w19_64
    have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K20.w32 (by decide) (by decide)).trans w19_68
    have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K20.w32 (by decide) (by decide)).trans w19_6c
    have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K20.w32 (by decide) (by decide)).trans w19_70
    have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K20.w32 (by decide) (by decide)).trans w19_74
    have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K20.w32 (by decide) (by decide)).trans w19_78
    have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K20.w32 (by decide) (by decide)).trans w19_7c
    have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K20.w32 (by decide) (by decide)).trans w19_80
    have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K20.w32 (by decide) (by decide)).trans w19_84
    have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K20.w32 (by decide) (by decide)).trans w19_88
    have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K20.w32 (by decide) (by decide)).trans w19_8c
    have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K20.w32 (by decide) (by decide)).trans w19_90
    have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K20.w32 (by decide) (by decide)).trans w19_94
    have w20_98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K20.w32 (by decide) (by decide)).trans w19_98
    have w20_9c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K20.w32 (by decide) (by decide)).trans w19_9c
    have w20_a0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K20.w32 (by decide) (by decide)).trans w19_a0
    have w20_a4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K20.w32 (by decide) (by decide)).trans w19_a4
    have w20_150 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K20.w32 (by decide) (by decide)).trans w19_150
    have w20_154 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K20.w32 (by decide) (by decide)).trans w19_154
    have w20_158 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K20.w32 (by decide) (by decide)).trans w19_158
    have w20_15c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K20.w32 (by decide) (by decide)).trans w19_15c
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K20.w32 (by decide) (by decide)).trans w19_420
    clear w19_420 w19_15c w19_158 w19_154 w19_150 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_30 w19_2c g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
    -- 0x944: lw
    obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g20_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s21 : St n21.mem SV n21 0x946 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
    have g21_9 : reg n21 (9 : Fin 32) = tbp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = dg := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = rootp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = ll := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = sgp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = kp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = sgl := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = tbl := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x44, 0x4)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m21]; exact w20_2c
    have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m21]; exact w20_30
    have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = 0 := by rw [m21]; exact w20_38
    have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m21]; exact w20_3c
    have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m21]; exact w20_40
    have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m21]; exact w20_48
    have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m21]; exact w20_4c
    have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m21]; exact w20_50
    have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m21]; exact w20_54
    have w21_58 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m21]; exact w20_58
    have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m21]; exact w20_5c
    have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m21]; exact w20_60
    have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m21]; exact w20_64
    have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m21]; exact w20_68
    have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m21]; exact w20_6c
    have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m21]; exact w20_70
    have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m21]; exact w20_74
    have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m21]; exact w20_78
    have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m21]; exact w20_7c
    have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m21]; exact w20_80
    have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m21]; exact w20_84
    have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m21]; exact w20_88
    have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m21]; exact w20_8c
    have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m21]; exact w20_90
    have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m21]; exact w20_94
    have w21_98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m21]; exact w20_98
    have w21_9c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m21]; exact w20_9c
    have w21_a0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m21]; exact w20_a0
    have w21_a4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m21]; exact w20_a4
    have w21_150 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m21]; exact w20_150
    have w21_154 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m21]; exact w20_154
    have w21_158 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m21]; exact w20_158
    have w21_15c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m21]; exact w20_15c
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m21]; exact w20_420
    clear w20_420 w20_15c w20_158 w20_154 w20_150 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_40 w20_3c w20_38 w20_30 w20_2c g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 rg20 W20 K20 fr20 s20 d20
    -- 0x946: j
    obtain ⟨n22, d22, u22⟩ := s21.jump E21.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s21.pc]; decide)
    have s22 : St n22.mem SV n22 0x7A4 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
    have g22_9 : reg n22 (9 : Fin 32) = tbp := by rw [u22.regs, g21_9]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [u22.regs, g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [u22.regs, g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [u22.regs, g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = sgp := by rw [u22.regs, g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = kp := by rw [u22.regs, g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = sgl := by rw [u22.regs, g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u22.regs, g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = tbl := by rw [u22.regs, g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x44, 0x4)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m22]; exact w21_2c
    have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m22]; exact w21_30
    have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = 0 := by rw [m22]; exact w21_38
    have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m22]; exact w21_3c
    have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m22]; exact w21_40
    have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m22]; exact w21_48
    have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m22]; exact w21_4c
    have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m22]; exact w21_50
    have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m22]; exact w21_54
    have w22_58 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m22]; exact w21_58
    have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m22]; exact w21_5c
    have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m22]; exact w21_60
    have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m22]; exact w21_64
    have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m22]; exact w21_68
    have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m22]; exact w21_6c
    have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m22]; exact w21_70
    have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m22]; exact w21_74
    have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m22]; exact w21_78
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m22]; exact w21_7c
    have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m22]; exact w21_80
    have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m22]; exact w21_84
    have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m22]; exact w21_88
    have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m22]; exact w21_8c
    have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m22]; exact w21_90
    have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m22]; exact w21_94
    have w22_98 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m22]; exact w21_98
    have w22_9c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m22]; exact w21_9c
    have w22_a0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m22]; exact w21_a0
    have w22_a4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m22]; exact w21_a4
    have w22_150 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m22]; exact w21_150
    have w22_154 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m22]; exact w21_154
    have w22_158 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m22]; exact w21_158
    have w22_15c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m22]; exact w21_15c
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m22]; exact w21_420
    clear w21_420 w21_15c w21_158 w21_154 w21_150 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_40 w21_3c w21_38 w21_30 w21_2c g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
    exact .inl ⟨(fun ⟨h0', tb7', h1', vp14', vl14', h2', _⟩ => by rw [hr7] at h0'; cases h0'; rw [htb7] at h1'; cases h1'; rw [hr14] at h2'; cases h2'), sv_fail F E22 s22 t22 (fun x hx => (fR22 x hx).trans (fM x hx).symm) V22 hret g22_2 g22_18 hO g22_3 g22_4⟩
  obtain ⟨te14, ht14, -, -⟩ := content_ok_elem hr14
  obtain ⟨p0_14, p4_14⟩ := Ok14 vp14 vl14 hr14
  obtain ⟨d8_14, d12_14⟩ := A14 te14 ht14
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8)] := keep_kk13.trans K14
  clear keep_kk13
  have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K14.w32 (by decide) (by decide)).trans w13_2c
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K14.w32 (by decide) (by decide)).trans w13_30
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K14.w32 (by decide) (by decide)).trans w13_3c
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K14.w32 (by decide) (by decide)).trans w13_40
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := (K14.w32 (by decide) (by decide)).trans w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K14.w32 (by decide) (by decide)).trans w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K14.w32 (by decide) (by decide)).trans w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K14.w32 (by decide) (by decide)).trans w13_50
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K14.w32 (by decide) (by decide)).trans w13_54
  have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K14.w32 (by decide) (by decide)).trans w13_58
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K14.w32 (by decide) (by decide)).trans w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K14.w32 (by decide) (by decide)).trans w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K14.w32 (by decide) (by decide)).trans w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K14.w32 (by decide) (by decide)).trans w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K14.w32 (by decide) (by decide)).trans w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K14.w32 (by decide) (by decide)).trans w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K14.w32 (by decide) (by decide)).trans w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K14.w32 (by decide) (by decide)).trans w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K14.w32 (by decide) (by decide)).trans w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K14.w32 (by decide) (by decide)).trans w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K14.w32 (by decide) (by decide)).trans w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K14.w32 (by decide) (by decide)).trans w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K14.w32 (by decide) (by decide)).trans w13_8c
  have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K14.w32 (by decide) (by decide)).trans w13_90
  have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K14.w32 (by decide) (by decide)).trans w13_94
  have w14_98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K14.w32 (by decide) (by decide)).trans w13_98
  have w14_9c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K14.w32 (by decide) (by decide)).trans w13_9c
  have w14_a0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K14.w32 (by decide) (by decide)).trans w13_a0
  have w14_a4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K14.w32 (by decide) (by decide)).trans w13_a4
  have w14_150 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K14.w32 (by decide) (by decide)).trans w13_150
  have w14_154 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K14.w32 (by decide) (by decide)).trans w13_154
  have w14_158 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K14.w32 (by decide) (by decide)).trans w13_158
  have w14_15c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K14.w32 (by decide) (by decide)).trans w13_15c
  have w14_408 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := d8_14
  have w14_40c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := d12_14
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := p0_14
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := p4_14
  clear w13_40c w13_408 w13_15c w13_158 w13_154 w13_150 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_44 w13_40 w13_3c w13_30 w13_2c g13_11 g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x46C: lw
  obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_46c (off' := 0x470) (by decide)
    (by rw [g14_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s15 : St n15.mem SV n15 0x470 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_9 : reg n15 (9 : Fin 32) = tbp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = dg := by rw [u15.regs, upd_ne (by decide) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = rootp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = ll := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = sgp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = kp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = sgl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = tbl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_10 : reg n15 a0 = vp14 := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w14_420]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m15]; exact w14_2c
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m15]; exact w14_30
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m15]; exact w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m15]; exact w14_40
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m15]; exact w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m15]; exact w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m15]; exact w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m15]; exact w14_50
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m15]; exact w14_54
  have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m15]; exact w14_58
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m15]; exact w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m15]; exact w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m15]; exact w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m15]; exact w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m15]; exact w14_70
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m15]; exact w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m15]; exact w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m15]; exact w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m15]; exact w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m15]; exact w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m15]; exact w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m15]; exact w14_8c
  have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m15]; exact w14_90
  have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m15]; exact w14_94
  have w15_98 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m15]; exact w14_98
  have w15_9c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m15]; exact w14_9c
  have w15_a0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m15]; exact w14_a0
  have w15_a4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m15]; exact w14_a4
  have w15_150 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m15]; exact w14_150
  have w15_154 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m15]; exact w14_154
  have w15_158 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m15]; exact w14_158
  have w15_15c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m15]; exact w14_15c
  have w15_408 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m15]; exact w14_408
  have w15_40c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m15]; exact w14_40c
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m15]; exact w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m15]; exact w14_424
  clear w14_424 w14_420 w14_40c w14_408 w14_15c w14_158 w14_154 w14_150 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_30 w14_2c d12_14 d8_14 p4_14 p0_14 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 Er14 Ok14 A14 K14 rk14 sp14 s14 c14
  -- 0x470: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_470 (off' := 0x472) (c := 0x38)
    (by decide) (by rw [g15_2]; sv_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_9 : reg n16 (9 : Fin 32) = tbp := by rw [rg16 (9 : Fin 32), g15_9]
  have g16_10 : reg n16 a0 = vp14 := by rw [rg16 a0, g15_10]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = dg := by rw [rg16 (20 : Fin 32), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = rootp := by rw [rg16 (21 : Fin 32), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = ll := by rw [rg16 (22 : Fin 32), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = sgp := by rw [rg16 (23 : Fin 32), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = kp := by rw [rg16 (24 : Fin 32), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = sgl := by rw [rg16 (25 : Fin 32), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg16 (26 : Fin 32), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = tbl := by rw [rg16 (27 : Fin 32), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K16.w32 (by decide) (by decide)).trans w15_2c
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K16.w32 (by decide) (by decide)).trans w15_30
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K16.w32 (by decide) (by decide)).trans w15_3c
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K16.w32 (by decide) (by decide)).trans w15_40
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := (K16.w32 (by decide) (by decide)).trans w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K16.w32 (by decide) (by decide)).trans w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K16.w32 (by decide) (by decide)).trans w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K16.w32 (by decide) (by decide)).trans w15_50
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K16.w32 (by decide) (by decide)).trans w15_54
  have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K16.w32 (by decide) (by decide)).trans w15_58
  have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K16.w32 (by decide) (by decide)).trans w15_5c
  have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K16.w32 (by decide) (by decide)).trans w15_60
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K16.w32 (by decide) (by decide)).trans w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K16.w32 (by decide) (by decide)).trans w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K16.w32 (by decide) (by decide)).trans w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K16.w32 (by decide) (by decide)).trans w15_70
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K16.w32 (by decide) (by decide)).trans w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K16.w32 (by decide) (by decide)).trans w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K16.w32 (by decide) (by decide)).trans w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K16.w32 (by decide) (by decide)).trans w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K16.w32 (by decide) (by decide)).trans w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K16.w32 (by decide) (by decide)).trans w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K16.w32 (by decide) (by decide)).trans w15_8c
  have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K16.w32 (by decide) (by decide)).trans w15_90
  have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K16.w32 (by decide) (by decide)).trans w15_94
  have w16_98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K16.w32 (by decide) (by decide)).trans w15_98
  have w16_9c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K16.w32 (by decide) (by decide)).trans w15_9c
  have w16_a0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K16.w32 (by decide) (by decide)).trans w15_a0
  have w16_a4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K16.w32 (by decide) (by decide)).trans w15_a4
  have w16_150 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K16.w32 (by decide) (by decide)).trans w15_150
  have w16_154 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K16.w32 (by decide) (by decide)).trans w15_154
  have w16_158 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K16.w32 (by decide) (by decide)).trans w15_158
  have w16_15c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K16.w32 (by decide) (by decide)).trans w15_15c
  have w16_408 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := (K16.w32 (by decide) (by decide)).trans w15_408
  have w16_40c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := (K16.w32 (by decide) (by decide)).trans w15_40c
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := (K16.w32 (by decide) (by decide)).trans w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := (K16.w32 (by decide) (by decide)).trans w15_424
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [W16, g15_10]
  clear w15_424 w15_420 w15_40c w15_408 w15_15c w15_158 w15_154 w15_150 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_30 w15_2c g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0x472: branch, not taken
  obtain ⟨n17, d17, u17⟩ := s16.notTaken E16.self 0x476 sv_at_472
    (by decide) (by rw [g16_10, s16.zero]; exact br_beq_f (((in2.restW htb7).contentIn hr14).pos_ne))
  have s17 : St n17.mem SV n17 0x476 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
  have g17_9 : reg n17 (9 : Fin 32) = tbp := by rw [u17.regs, g16_9]
  have g17_10 : reg n17 a0 = vp14 := by rw [u17.regs, g16_10]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [u17.regs, g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [u17.regs, g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [u17.regs, g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = sgp := by rw [u17.regs, g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = kp := by rw [u17.regs, g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = sgl := by rw [u17.regs, g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u17.regs, g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = tbl := by rw [u17.regs, g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m17]; exact w16_2c
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m17]; exact w16_30
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m17]; exact w16_38
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m17]; exact w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m17]; exact w16_40
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m17]; exact w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m17]; exact w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m17]; exact w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m17]; exact w16_50
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m17]; exact w16_54
  have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m17]; exact w16_58
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m17]; exact w16_5c
  have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m17]; exact w16_60
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m17]; exact w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m17]; exact w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m17]; exact w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m17]; exact w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m17]; exact w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m17]; exact w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m17]; exact w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m17]; exact w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m17]; exact w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m17]; exact w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m17]; exact w16_8c
  have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m17]; exact w16_90
  have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m17]; exact w16_94
  have w17_98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m17]; exact w16_98
  have w17_9c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m17]; exact w16_9c
  have w17_a0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m17]; exact w16_a0
  have w17_a4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m17]; exact w16_a4
  have w17_150 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m17]; exact w16_150
  have w17_154 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m17]; exact w16_154
  have w17_158 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m17]; exact w16_158
  have w17_15c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m17]; exact w16_15c
  have w17_408 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m17]; exact w16_408
  have w17_40c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m17]; exact w16_40c
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m17]; exact w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m17]; exact w16_424
  clear w16_38 w16_424 w16_420 w16_40c w16_408 w16_15c w16_158 w16_154 w16_150 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_30 w16_2c g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_10 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0x476: lw
  obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_476 (off' := 0x47A) (by decide)
    (by rw [g17_2, show B + 0x21A0 + 0x40C = B + 0x21A0 + BitVec.ofNat 32 0x40C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s18 : St n18.mem SV n18 0x47A (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
  have g18_9 : reg n18 (9 : Fin 32) = tbp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [u18.regs, upd_ne (by decide) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = sgp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = kp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = sgl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = tbl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
  have g18_10 : reg n18 a0 = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by
    rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g17_2, show B + 0x21A0 + 0x40C = B + 0x21A0 + BitVec.ofNat 32 0x40C by sv_addr, w17_40c]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m18]; exact w17_2c
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m18]; exact w17_30
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m18]; exact w17_38
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m18]; exact w17_3c
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m18]; exact w17_40
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m18]; exact w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m18]; exact w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m18]; exact w17_4c
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m18]; exact w17_50
  have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m18]; exact w17_54
  have w18_58 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m18]; exact w17_58
  have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m18]; exact w17_5c
  have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m18]; exact w17_60
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m18]; exact w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m18]; exact w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m18]; exact w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m18]; exact w17_70
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m18]; exact w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m18]; exact w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m18]; exact w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m18]; exact w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m18]; exact w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m18]; exact w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m18]; exact w17_8c
  have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m18]; exact w17_90
  have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m18]; exact w17_94
  have w18_98 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m18]; exact w17_98
  have w18_9c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m18]; exact w17_9c
  have w18_a0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m18]; exact w17_a0
  have w18_a4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m18]; exact w17_a4
  have w18_150 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m18]; exact w17_150
  have w18_154 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m18]; exact w17_154
  have w18_158 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m18]; exact w17_158
  have w18_15c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m18]; exact w17_15c
  have w18_408 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m18]; exact w17_408
  have w18_40c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m18]; exact w17_40c
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m18]; exact w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m18]; exact w17_424
  clear w17_424 w17_420 w17_40c w17_408 w17_15c w17_158 w17_154 w17_150 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_30 w17_2c g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_10 g17_9 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  by_cases hz_18 : ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) = 0
  rotate_left
  · -- 0x47A: branch, taken
    obtain ⟨n19, d19, u19⟩ := s18.taken E18.self 0x940 sv_at_47a
      (by decide) (by rw [g18_10, s18.zero]; exact br_bne_t hz_18)
    have s19 : St n19.mem SV n19 0x940 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
    have g19_9 : reg n19 (9 : Fin 32) = tbp := by rw [u19.regs, g18_9]
    have g19_10 : reg n19 a0 = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [u19.regs, g18_10]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = dg := by rw [u19.regs, g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = rootp := by rw [u19.regs, g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = ll := by rw [u19.regs, g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = sgp := by rw [u19.regs, g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = kp := by rw [u19.regs, g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = sgl := by rw [u19.regs, g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u19.regs, g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = tbl := by rw [u19.regs, g18_27]
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m19]; exact w18_2c
    have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m19]; exact w18_30
    have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m19]; exact w18_38
    have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m19]; exact w18_3c
    have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m19]; exact w18_40
    have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m19]; exact w18_44
    have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m19]; exact w18_48
    have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m19]; exact w18_4c
    have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m19]; exact w18_50
    have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m19]; exact w18_54
    have w19_58 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m19]; exact w18_58
    have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m19]; exact w18_5c
    have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m19]; exact w18_60
    have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m19]; exact w18_64
    have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m19]; exact w18_68
    have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m19]; exact w18_6c
    have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m19]; exact w18_70
    have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m19]; exact w18_74
    have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m19]; exact w18_78
    have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m19]; exact w18_7c
    have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m19]; exact w18_80
    have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m19]; exact w18_84
    have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m19]; exact w18_88
    have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m19]; exact w18_8c
    have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m19]; exact w18_90
    have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m19]; exact w18_94
    have w19_98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m19]; exact w18_98
    have w19_9c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m19]; exact w18_9c
    have w19_a0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m19]; exact w18_a0
    have w19_a4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m19]; exact w18_a4
    have w19_150 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m19]; exact w18_150
    have w19_154 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m19]; exact w18_154
    have w19_158 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m19]; exact w18_158
    have w19_15c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m19]; exact w18_15c
    have w19_408 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m19]; exact w18_408
    have w19_40c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m19]; exact w18_40c
    have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m19]; exact w18_420
    have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m19]; exact w18_424
    clear w18_424 w18_420 w18_40c w18_408 w18_15c w18_158 w18_154 w18_150 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_30 w18_2c g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    -- 0x940
    obtain ⟨n20, c20, u20⟩ := s19.block svX2c940 E19.self svX2c940_end
      ⟨trivial, trivial⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have s20 : St n20.mem SV n20 0x942 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have rb20 : ∀ q, reg n20 q = (runBlock svX2c940 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
    have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
    have t20 : Steps n0 n20 := t19.trans c20
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.same m20
    have g20_2 : reg n20 sp = B + 0x21A0 := by
      rw [rb20, runBlock_reg _ _ _ sp s19.zero (by decide), g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb20, runBlock_reg _ _ _ (3 : Fin 32) s19.zero (by decide), g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb20, runBlock_reg _ _ _ (4 : Fin 32) s19.zero (by decide), g19_4]
    have g20_9 : reg n20 (9 : Fin 32) = tbp := by
      rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
    have g20_18 : reg n20 (18 : Fin 32) = out := by
      rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by
      rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
    have g20_20 : reg n20 (20 : Fin 32) = dg := by
      rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
    have g20_21 : reg n20 (21 : Fin 32) = rootp := by
      rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = ll := by
      rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = sgp := by
      rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = kp := by
      rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = sgl := by
      rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = tbl := by
      rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
    have g20_10 : reg n20 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb20]; simp +decide only [runBlock, BInstr.run, svX2c940, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g19_2, g19_3, g19_4, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m20]; exact w19_2c
    have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m20]; exact w19_30
    have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m20]; exact w19_38
    have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m20]; exact w19_3c
    have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m20]; exact w19_40
    have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m20]; exact w19_44
    have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m20]; exact w19_48
    have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m20]; exact w19_4c
    have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m20]; exact w19_50
    have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m20]; exact w19_54
    have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m20]; exact w19_58
    have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m20]; exact w19_5c
    have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m20]; exact w19_60
    have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m20]; exact w19_64
    have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m20]; exact w19_68
    have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m20]; exact w19_6c
    have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m20]; exact w19_70
    have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m20]; exact w19_74
    have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m20]; exact w19_78
    have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m20]; exact w19_7c
    have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m20]; exact w19_80
    have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m20]; exact w19_84
    have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m20]; exact w19_88
    have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m20]; exact w19_8c
    have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m20]; exact w19_90
    have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m20]; exact w19_94
    have w20_98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m20]; exact w19_98
    have w20_9c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m20]; exact w19_9c
    have w20_a0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m20]; exact w19_a0
    have w20_a4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m20]; exact w19_a4
    have w20_150 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m20]; exact w19_150
    have w20_154 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m20]; exact w19_154
    have w20_158 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m20]; exact w19_158
    have w20_15c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m20]; exact w19_15c
    have w20_408 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m20]; exact w19_408
    have w20_40c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m20]; exact w19_40c
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m20]; exact w19_420
    have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m20]; exact w19_424
    clear w19_424 w19_420 w19_40c w19_408 w19_15c w19_158 w19_154 w19_150 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_30 w19_2c g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_10 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
    -- 0x942: sw
    obtain ⟨n21, d21, s21, fr21, K21, W21, rg21⟩ := sv_sw F E20 s20 sv_at_942 (off' := 0x944) (c := 0x44)
      (by decide) (by rw [g20_2]; sv_addr) (by decide) (by decide)
    have t21 : Steps n0 n21 := t20.trans d21
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.keep K21 (by decide)
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rg21 sp, g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg21 (3 : Fin 32), g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg21 (4 : Fin 32), g20_4]
    have g21_9 : reg n21 (9 : Fin 32) = tbp := by rw [rg21 (9 : Fin 32), g20_9]
    have g21_10 : reg n21 a0 = BitVec.ofNat 32 0x1 := by rw [rg21 a0, g20_10]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rg21 (18 : Fin 32), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rg21 (19 : Fin 32), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = dg := by rw [rg21 (20 : Fin 32), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = rootp := by rw [rg21 (21 : Fin 32), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = ll := by rw [rg21 (22 : Fin 32), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = sgp := by rw [rg21 (23 : Fin 32), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = kp := by rw [rg21 (24 : Fin 32), g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = sgl := by rw [rg21 (25 : Fin 32), g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg21 (26 : Fin 32), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = tbl := by rw [rg21 (27 : Fin 32), g20_27]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x44, 0x4)] := keep_kk20.trans K21.toL
    clear keep_kk20
    have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K21.w32 (by decide) (by decide)).trans w20_2c
    have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K21.w32 (by decide) (by decide)).trans w20_30
    have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := (K21.w32 (by decide) (by decide)).trans w20_38
    have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K21.w32 (by decide) (by decide)).trans w20_3c
    have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K21.w32 (by decide) (by decide)).trans w20_40
    have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K21.w32 (by decide) (by decide)).trans w20_48
    have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K21.w32 (by decide) (by decide)).trans w20_4c
    have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K21.w32 (by decide) (by decide)).trans w20_50
    have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K21.w32 (by decide) (by decide)).trans w20_54
    have w21_58 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K21.w32 (by decide) (by decide)).trans w20_58
    have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K21.w32 (by decide) (by decide)).trans w20_5c
    have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K21.w32 (by decide) (by decide)).trans w20_60
    have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K21.w32 (by decide) (by decide)).trans w20_64
    have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K21.w32 (by decide) (by decide)).trans w20_68
    have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K21.w32 (by decide) (by decide)).trans w20_6c
    have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K21.w32 (by decide) (by decide)).trans w20_70
    have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K21.w32 (by decide) (by decide)).trans w20_74
    have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K21.w32 (by decide) (by decide)).trans w20_78
    have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K21.w32 (by decide) (by decide)).trans w20_7c
    have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K21.w32 (by decide) (by decide)).trans w20_80
    have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K21.w32 (by decide) (by decide)).trans w20_84
    have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K21.w32 (by decide) (by decide)).trans w20_88
    have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K21.w32 (by decide) (by decide)).trans w20_8c
    have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K21.w32 (by decide) (by decide)).trans w20_90
    have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K21.w32 (by decide) (by decide)).trans w20_94
    have w21_98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K21.w32 (by decide) (by decide)).trans w20_98
    have w21_9c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K21.w32 (by decide) (by decide)).trans w20_9c
    have w21_a0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K21.w32 (by decide) (by decide)).trans w20_a0
    have w21_a4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K21.w32 (by decide) (by decide)).trans w20_a4
    have w21_150 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K21.w32 (by decide) (by decide)).trans w20_150
    have w21_154 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K21.w32 (by decide) (by decide)).trans w20_154
    have w21_158 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K21.w32 (by decide) (by decide)).trans w20_158
    have w21_15c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K21.w32 (by decide) (by decide)).trans w20_15c
    have w21_408 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := (K21.w32 (by decide) (by decide)).trans w20_408
    have w21_40c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := (K21.w32 (by decide) (by decide)).trans w20_40c
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := (K21.w32 (by decide) (by decide)).trans w20_420
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := (K21.w32 (by decide) (by decide)).trans w20_424
    have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [W21, g20_10]
    clear w20_424 w20_420 w20_40c w20_408 w20_15c w20_158 w20_154 w20_150 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_30 w20_2c g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
    -- 0x944: lw
    obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g21_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s22 : St n22.mem SV n22 0x946 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
    have g22_9 : reg n22 (9 : Fin 32) = tbp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
    have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x1 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_10]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = sgp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = kp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = sgl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = tbl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x44, 0x4)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m22]; exact w21_2c
    have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m22]; exact w21_30
    have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m22]; exact w21_38
    have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m22]; exact w21_3c
    have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m22]; exact w21_40
    have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m22]; exact w21_44
    have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m22]; exact w21_48
    have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m22]; exact w21_4c
    have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m22]; exact w21_50
    have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m22]; exact w21_54
    have w22_58 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m22]; exact w21_58
    have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m22]; exact w21_5c
    have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m22]; exact w21_60
    have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m22]; exact w21_64
    have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m22]; exact w21_68
    have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m22]; exact w21_6c
    have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m22]; exact w21_70
    have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m22]; exact w21_74
    have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m22]; exact w21_78
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m22]; exact w21_7c
    have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m22]; exact w21_80
    have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m22]; exact w21_84
    have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m22]; exact w21_88
    have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m22]; exact w21_8c
    have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m22]; exact w21_90
    have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m22]; exact w21_94
    have w22_98 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m22]; exact w21_98
    have w22_9c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m22]; exact w21_9c
    have w22_a0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m22]; exact w21_a0
    have w22_a4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m22]; exact w21_a4
    have w22_150 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m22]; exact w21_150
    have w22_154 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m22]; exact w21_154
    have w22_158 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m22]; exact w21_158
    have w22_15c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m22]; exact w21_15c
    have w22_408 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m22]; exact w21_408
    have w22_40c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m22]; exact w21_40c
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m22]; exact w21_420
    have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m22]; exact w21_424
    clear w21_44 w21_424 w21_420 w21_40c w21_408 w21_15c w21_158 w21_154 w21_150 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_40 w21_3c w21_38 w21_30 w21_2c g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_10 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 rg21 W21 K21 fr21 s21 d21
    -- 0x946: j
    obtain ⟨n23, d23, u23⟩ := s22.jump E22.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s22.pc]; decide)
    have s23 : St n23.mem SV n23 0x7A4 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
    have t23 : Steps n0 n23 := t22.trans (.single d23)
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.same m23
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, g22_4]
    have g23_9 : reg n23 (9 : Fin 32) = tbp := by rw [u23.regs, g22_9]
    have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x1 := by rw [u23.regs, g22_10]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = dg := by rw [u23.regs, g22_20]
    have g23_21 : reg n23 (21 : Fin 32) = rootp := by rw [u23.regs, g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = ll := by rw [u23.regs, g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = sgp := by rw [u23.regs, g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = kp := by rw [u23.regs, g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = sgl := by rw [u23.regs, g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u23.regs, g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = tbl := by rw [u23.regs, g22_27]
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x44, 0x4)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m23]; exact w22_2c
    have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m23]; exact w22_30
    have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m23]; exact w22_38
    have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m23]; exact w22_3c
    have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m23]; exact w22_40
    have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m23]; exact w22_44
    have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m23]; exact w22_48
    have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m23]; exact w22_4c
    have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m23]; exact w22_50
    have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m23]; exact w22_54
    have w23_58 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m23]; exact w22_58
    have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m23]; exact w22_5c
    have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m23]; exact w22_60
    have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m23]; exact w22_64
    have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m23]; exact w22_68
    have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m23]; exact w22_6c
    have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m23]; exact w22_70
    have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m23]; exact w22_74
    have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m23]; exact w22_78
    have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m23]; exact w22_7c
    have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m23]; exact w22_80
    have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m23]; exact w22_84
    have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m23]; exact w22_88
    have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m23]; exact w22_8c
    have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m23]; exact w22_90
    have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m23]; exact w22_94
    have w23_98 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m23]; exact w22_98
    have w23_9c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m23]; exact w22_9c
    have w23_a0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m23]; exact w22_a0
    have w23_a4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m23]; exact w22_a4
    have w23_150 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m23]; exact w22_150
    have w23_154 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m23]; exact w22_154
    have w23_158 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m23]; exact w22_158
    have w23_15c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m23]; exact w22_15c
    have w23_408 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m23]; exact w22_408
    have w23_40c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m23]; exact w22_40c
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m23]; exact w22_420
    have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m23]; exact w22_424
    clear w22_424 w22_420 w22_40c w22_408 w22_15c w22_158 w22_154 w22_150 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_30 w22_2c g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    exact .inl ⟨(fun ⟨h0', tb7', h1', vp14', vl14', h2', te14', h3', h4', _⟩ => by rw [hr7] at h0'; cases h0'; rw [htb7] at h1'; cases h1'; rw [hr14] at h2'; cases h2'; rw [ht14] at h3'; cases h3'; exact hz_18 h4'), sv_fail F E23 s23 t23 (fun x hx => (fR23 x hx).trans (fM x hx).symm) V23 hret g23_2 g23_18 hO g23_3 g23_4⟩
  -- 0x47A: branch, not taken
  obtain ⟨n19, d19, u19⟩ := s18.notTaken E18.self 0x47E sv_at_47a
    (by decide) (by rw [g18_10, s18.zero]; exact br_bne_f hz_18)
  have s19 : St n19.mem SV n19 0x47E (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
  have g19_9 : reg n19 (9 : Fin 32) = tbp := by rw [u19.regs, g18_9]
  have g19_10 : reg n19 a0 = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [u19.regs, g18_10]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = dg := by rw [u19.regs, g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = rootp := by rw [u19.regs, g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = ll := by rw [u19.regs, g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = sgp := by rw [u19.regs, g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = kp := by rw [u19.regs, g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = sgl := by rw [u19.regs, g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u19.regs, g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = tbl := by rw [u19.regs, g18_27]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m19]; exact w18_2c
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m19]; exact w18_30
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m19]; exact w18_38
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m19]; exact w18_3c
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m19]; exact w18_40
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m19]; exact w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m19]; exact w18_48
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m19]; exact w18_4c
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m19]; exact w18_50
  have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m19]; exact w18_54
  have w19_58 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m19]; exact w18_58
  have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m19]; exact w18_5c
  have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m19]; exact w18_60
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m19]; exact w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m19]; exact w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m19]; exact w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m19]; exact w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m19]; exact w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m19]; exact w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m19]; exact w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m19]; exact w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m19]; exact w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m19]; exact w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m19]; exact w18_8c
  have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m19]; exact w18_90
  have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m19]; exact w18_94
  have w19_98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m19]; exact w18_98
  have w19_9c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m19]; exact w18_9c
  have w19_a0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m19]; exact w18_a0
  have w19_a4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m19]; exact w18_a4
  have w19_150 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m19]; exact w18_150
  have w19_154 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m19]; exact w18_154
  have w19_158 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m19]; exact w18_158
  have w19_15c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m19]; exact w18_15c
  have w19_408 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m19]; exact w18_408
  have w19_40c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m19]; exact w18_40c
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m19]; exact w18_424
  clear w18_424 w18_420 w18_40c w18_408 w18_15c w18_158 w18_154 w18_150 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_30 w18_2c g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x47E: lw
  obtain ⟨n20, d20, u20⟩ := s19.lw E19.self sv_at_47e (off' := 0x482) (by decide)
    (by rw [g19_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s20 : St n20.mem SV n20 0x482 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_4]
  have g20_9 : reg n20 (9 : Fin 32) = tbp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, upd_ne (by decide) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = dg := by rw [u20.regs, upd_ne (by decide) (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = rootp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = ll := by rw [u20.regs, upd_ne (by decide) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = sgp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = kp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = sgl := by rw [u20.regs, upd_ne (by decide) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = tbl := by rw [u20.regs, upd_ne (by decide) (by decide), g19_27]
  have g20_10 : reg n20 a0 = vl14 := by
    rw [u20.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g19_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w19_424]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m20]; exact w19_2c
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m20]; exact w19_30
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m20]; exact w19_38
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m20]; exact w19_3c
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m20]; exact w19_40
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m20]; exact w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m20]; exact w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m20]; exact w19_4c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m20]; exact w19_50
  have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m20]; exact w19_54
  have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m20]; exact w19_58
  have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m20]; exact w19_5c
  have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m20]; exact w19_60
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m20]; exact w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m20]; exact w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m20]; exact w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m20]; exact w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m20]; exact w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m20]; exact w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m20]; exact w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m20]; exact w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m20]; exact w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m20]; exact w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m20]; exact w19_8c
  have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m20]; exact w19_90
  have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m20]; exact w19_94
  have w20_98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m20]; exact w19_98
  have w20_9c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m20]; exact w19_9c
  have w20_a0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m20]; exact w19_a0
  have w20_a4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m20]; exact w19_a4
  have w20_150 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m20]; exact w19_150
  have w20_154 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m20]; exact w19_154
  have w20_158 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m20]; exact w19_158
  have w20_15c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m20]; exact w19_15c
  have w20_408 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m20]; exact w19_408
  have w20_40c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m20]; exact w19_40c
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m20]; exact w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m20]; exact w19_424
  clear w19_424 w19_420 w19_40c w19_408 w19_15c w19_158 w19_154 w19_150 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_30 w19_2c g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_10 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x482: sw
  obtain ⟨n21, d21, s21, fr21, K21, W21, rg21⟩ := sv_sw F E20 s20 sv_at_482 (off' := 0x484) (c := 0x34)
    (by decide) (by rw [g20_2]; sv_addr) (by decide) (by decide)
  have t21 : Steps n0 n21 := t20.trans d21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keep K21 (by decide)
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rg21 sp, g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg21 (3 : Fin 32), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg21 (4 : Fin 32), g20_4]
  have g21_9 : reg n21 (9 : Fin 32) = tbp := by rw [rg21 (9 : Fin 32), g20_9]
  have g21_10 : reg n21 a0 = vl14 := by rw [rg21 a0, g20_10]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rg21 (18 : Fin 32), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rg21 (19 : Fin 32), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = dg := by rw [rg21 (20 : Fin 32), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = rootp := by rw [rg21 (21 : Fin 32), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = ll := by rw [rg21 (22 : Fin 32), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = sgp := by rw [rg21 (23 : Fin 32), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = kp := by rw [rg21 (24 : Fin 32), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = sgl := by rw [rg21 (25 : Fin 32), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg21 (26 : Fin 32), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = tbl := by rw [rg21 (27 : Fin 32), g20_27]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4)] := keep_kk20.trans K21.toL
  clear keep_kk20
  have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K21.w32 (by decide) (by decide)).trans w20_2c
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K21.w32 (by decide) (by decide)).trans w20_30
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := (K21.w32 (by decide) (by decide)).trans w20_38
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K21.w32 (by decide) (by decide)).trans w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K21.w32 (by decide) (by decide)).trans w20_40
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := (K21.w32 (by decide) (by decide)).trans w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K21.w32 (by decide) (by decide)).trans w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K21.w32 (by decide) (by decide)).trans w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K21.w32 (by decide) (by decide)).trans w20_50
  have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K21.w32 (by decide) (by decide)).trans w20_54
  have w21_58 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K21.w32 (by decide) (by decide)).trans w20_58
  have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K21.w32 (by decide) (by decide)).trans w20_5c
  have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K21.w32 (by decide) (by decide)).trans w20_60
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K21.w32 (by decide) (by decide)).trans w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K21.w32 (by decide) (by decide)).trans w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K21.w32 (by decide) (by decide)).trans w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K21.w32 (by decide) (by decide)).trans w20_70
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K21.w32 (by decide) (by decide)).trans w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K21.w32 (by decide) (by decide)).trans w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K21.w32 (by decide) (by decide)).trans w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K21.w32 (by decide) (by decide)).trans w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K21.w32 (by decide) (by decide)).trans w20_84
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K21.w32 (by decide) (by decide)).trans w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K21.w32 (by decide) (by decide)).trans w20_8c
  have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K21.w32 (by decide) (by decide)).trans w20_90
  have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K21.w32 (by decide) (by decide)).trans w20_94
  have w21_98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K21.w32 (by decide) (by decide)).trans w20_98
  have w21_9c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K21.w32 (by decide) (by decide)).trans w20_9c
  have w21_a0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K21.w32 (by decide) (by decide)).trans w20_a0
  have w21_a4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K21.w32 (by decide) (by decide)).trans w20_a4
  have w21_150 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K21.w32 (by decide) (by decide)).trans w20_150
  have w21_154 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K21.w32 (by decide) (by decide)).trans w20_154
  have w21_158 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K21.w32 (by decide) (by decide)).trans w20_158
  have w21_15c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K21.w32 (by decide) (by decide)).trans w20_15c
  have w21_408 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := (K21.w32 (by decide) (by decide)).trans w20_408
  have w21_40c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := (K21.w32 (by decide) (by decide)).trans w20_40c
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := (K21.w32 (by decide) (by decide)).trans w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := (K21.w32 (by decide) (by decide)).trans w20_424
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [W21, g20_10]
  clear w20_424 w20_420 w20_40c w20_408 w20_15c w20_158 w20_154 w20_150 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_30 w20_2c g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
  -- 0x484: lw
  obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_484 (off' := 0x486) (by decide)
    (by rw [g21_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s22 : St n22.mem SV n22 0x486 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
  have g22_9 : reg n22 (9 : Fin 32) = tbp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = sgp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = kp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = sgl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = tbl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
  have g22_10 : reg n22 a0 = rem := by
    rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g21_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w21_50]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m22]; exact w21_2c
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m22]; exact w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m22]; exact w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m22]; exact w21_38
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m22]; exact w21_3c
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m22]; exact w21_40
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m22]; exact w21_48
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m22]; exact w21_4c
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m22]; exact w21_50
  have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m22]; exact w21_54
  have w22_58 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m22]; exact w21_58
  have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m22]; exact w21_5c
  have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m22]; exact w21_60
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m22]; exact w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m22]; exact w21_68
  have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m22]; exact w21_6c
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m22]; exact w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m22]; exact w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m22]; exact w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m22]; exact w21_7c
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m22]; exact w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m22]; exact w21_84
  have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m22]; exact w21_88
  have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m22]; exact w21_8c
  have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m22]; exact w21_90
  have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m22]; exact w21_94
  have w22_98 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m22]; exact w21_98
  have w22_9c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m22]; exact w21_9c
  have w22_a0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m22]; exact w21_a0
  have w22_a4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m22]; exact w21_a4
  have w22_150 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m22]; exact w21_150
  have w22_154 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m22]; exact w21_154
  have w22_158 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m22]; exact w21_158
  have w22_15c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m22]; exact w21_15c
  have w22_408 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m22]; exact w21_408
  have w22_40c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m22]; exact w21_40c
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m22]; exact w21_424
  clear w21_34 w21_424 w21_420 w21_40c w21_408 w21_15c w21_158 w21_154 w21_150 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_30 w21_2c g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_10 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 rg21 W21 K21 fr21 s21 d21
  -- 0x486: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_486 (off' := 0x488) (by decide)
    (by rw [g22_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s23 : St n23.mem SV n23 0x488 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_9 : reg n23 (9 : Fin 32) = tbp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_10 : reg n23 a0 = rem := by rw [u23.regs, upd_ne (by decide) (by decide), g22_10]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = dg := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = rootp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = ll := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = sgp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = kp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = sgl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = tbl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_11 : reg n23 a1 = L := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr, w22_40]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m23]; exact w22_2c
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m23]; exact w22_38
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m23]; exact w22_3c
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m23]; exact w22_40
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m23]; exact w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m23]; exact w22_48
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m23]; exact w22_4c
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m23]; exact w22_50
  have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m23]; exact w22_54
  have w23_58 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m23]; exact w22_58
  have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m23]; exact w22_5c
  have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m23]; exact w22_60
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m23]; exact w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m23]; exact w22_68
  have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m23]; exact w22_6c
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m23]; exact w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m23]; exact w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m23]; exact w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m23]; exact w22_84
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m23]; exact w22_88
  have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m23]; exact w22_8c
  have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m23]; exact w22_90
  have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m23]; exact w22_94
  have w23_98 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m23]; exact w22_98
  have w23_9c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m23]; exact w22_9c
  have w23_a0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m23]; exact w22_a0
  have w23_a4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m23]; exact w22_a4
  have w23_150 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m23]; exact w22_150
  have w23_154 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m23]; exact w22_154
  have w23_158 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m23]; exact w22_158
  have w23_15c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m23]; exact w22_15c
  have w23_408 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m23]; exact w22_408
  have w23_40c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m23]; exact w22_40c
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m23]; exact w22_424
  clear w22_424 w22_420 w22_40c w22_408 w22_15c w22_158 w22_154 w22_150 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 w22_2c g22_10 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0x488
  obtain ⟨n24, c24, u24⟩ := s23.block svX2c488 E23.self svX2c488_end
    ⟨trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem SV n24 0x48A (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock svX2c488 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans c24
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by
    rw [rb24, runBlock_reg _ _ _ sp s23.zero (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (3 : Fin 32) s23.zero (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (4 : Fin 32) s23.zero (by decide), g23_4]
  have g24_9 : reg n24 (9 : Fin 32) = tbp := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
  have g24_10 : reg n24 a0 = rem := by
    rw [rb24, runBlock_reg _ _ _ a0 s23.zero (by decide), g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = dg := by
    rw [rb24, runBlock_reg _ _ _ (20 : Fin 32) s23.zero (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = rootp := by
    rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = ll := by
    rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = sgp := by
    rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = kp := by
    rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = sgl := by
    rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = tbl := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_11 : reg n24 a1 = (L) - (rem) := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svX2c488, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_9, g23_10, g23_11, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m24]; exact w23_2c
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m24]; exact w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m24]; exact w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m24]; exact w23_38
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m24]; exact w23_3c
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m24]; exact w23_40
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m24]; exact w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m24]; exact w23_48
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m24]; exact w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m24]; exact w23_50
  have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m24]; exact w23_54
  have w24_58 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m24]; exact w23_58
  have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m24]; exact w23_5c
  have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m24]; exact w23_60
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m24]; exact w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m24]; exact w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m24]; exact w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m24]; exact w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m24]; exact w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m24]; exact w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m24]; exact w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m24]; exact w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m24]; exact w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m24]; exact w23_8c
  have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m24]; exact w23_90
  have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m24]; exact w23_94
  have w24_98 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m24]; exact w23_98
  have w24_9c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m24]; exact w23_9c
  have w24_a0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m24]; exact w23_a0
  have w24_a4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m24]; exact w23_a4
  have w24_150 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m24]; exact w23_150
  have w24_154 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m24]; exact w23_154
  have w24_158 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m24]; exact w23_158
  have w24_15c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m24]; exact w23_15c
  have w24_408 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m24]; exact w23_408
  have w24_40c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m24]; exact w23_40c
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m24]; exact w23_424
  clear w23_424 w23_420 w23_40c w23_408 w23_15c w23_158 w23_154 w23_150 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 w23_2c g23_11 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_10 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  rw [sub_ofNat_toNat hle] at g24_11
  -- 0x48A: lw
  obtain ⟨n25, d25, u25⟩ := s24.lw E24.self sv_at_48a (off' := 0x48C) (by decide)
    (by rw [g24_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s25 : St n25.mem SV n25 0x48C (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans (.single d25)
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
  have g25_9 : reg n25 (9 : Fin 32) = tbp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_9]
  have g25_11 : reg n25 a1 = BitVec.ofNat 32 (L.toNat - rem.toNat) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_11]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = dg := by rw [u25.regs, upd_ne (by decide) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = rootp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = ll := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = sgp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = kp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = sgl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = tbl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
  have g25_10 : reg n25 a0 = p0 := by
    rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g24_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr, w24_3c]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m25]; exact w24_2c
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m25]; exact w24_30
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m25]; exact w24_34
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m25]; exact w24_38
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m25]; exact w24_3c
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m25]; exact w24_40
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m25]; exact w24_44
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m25]; exact w24_48
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m25]; exact w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m25]; exact w24_50
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m25]; exact w24_54
  have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m25]; exact w24_58
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m25]; exact w24_5c
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m25]; exact w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m25]; exact w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m25]; exact w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m25]; exact w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m25]; exact w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m25]; exact w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m25]; exact w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m25]; exact w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m25]; exact w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m25]; exact w24_84
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m25]; exact w24_88
  have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m25]; exact w24_8c
  have w25_90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m25]; exact w24_90
  have w25_94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m25]; exact w24_94
  have w25_98 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m25]; exact w24_98
  have w25_9c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m25]; exact w24_9c
  have w25_a0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m25]; exact w24_a0
  have w25_a4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m25]; exact w24_a4
  have w25_150 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m25]; exact w24_150
  have w25_154 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m25]; exact w24_154
  have w25_158 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m25]; exact w24_158
  have w25_15c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m25]; exact w24_15c
  have w25_408 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m25]; exact w24_408
  have w25_40c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m25]; exact w24_40c
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m25]; exact w24_420
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m25]; exact w24_424
  clear w24_424 w24_420 w24_40c w24_408 w24_15c w24_158 w24_154 w24_150 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 w24_2c g24_11 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_10 g24_9 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0x48C: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_48c (off' := 0x48E) (by decide)
    (by rw [g25_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0x48E (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_9 : reg n26 (9 : Fin 32) = tbp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
  have g26_10 : reg n26 a0 = p0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_10]
  have g26_11 : reg n26 a1 = BitVec.ofNat 32 (L.toNat - rem.toNat) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_11]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = dg := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = rootp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = ll := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = sgp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = kp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = sgl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = tbl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_12 : reg n26 a2 = op := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w25_4c]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m26]; exact w25_2c
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m26]; exact w25_30
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m26]; exact w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m26]; exact w25_38
  have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m26]; exact w25_3c
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m26]; exact w25_40
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m26]; exact w25_44
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m26]; exact w25_48
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m26]; exact w25_4c
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m26]; exact w25_50
  have w26_54 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m26]; exact w25_54
  have w26_58 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m26]; exact w25_58
  have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m26]; exact w25_5c
  have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m26]; exact w25_60
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m26]; exact w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m26]; exact w25_68
  have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m26]; exact w25_6c
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m26]; exact w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m26]; exact w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m26]; exact w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m26]; exact w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m26]; exact w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m26]; exact w25_84
  have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m26]; exact w25_88
  have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m26]; exact w25_8c
  have w26_90 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m26]; exact w25_90
  have w26_94 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m26]; exact w25_94
  have w26_98 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m26]; exact w25_98
  have w26_9c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m26]; exact w25_9c
  have w26_a0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m26]; exact w25_a0
  have w26_a4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m26]; exact w25_a4
  have w26_150 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m26]; exact w25_150
  have w26_154 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m26]; exact w25_154
  have w26_158 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m26]; exact w25_158
  have w26_15c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m26]; exact w25_15c
  have w26_408 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m26]; exact w25_408
  have w26_40c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m26]; exact w25_40c
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m26]; exact w25_420
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m26]; exact w25_424
  clear w25_424 w25_420 w25_40c w25_408 w25_15c w25_158 w25_154 w25_150 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_44 w25_40 w25_3c w25_38 w25_34 w25_30 w25_2c g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_11 g25_9 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
  -- 0x48E: lw
  obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_48e (off' := 0x490) (by decide)
    (by rw [g26_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s27 : St n27.mem SV n27 0x490 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
  have g27_9 : reg n27 (9 : Fin 32) = tbp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
  have g27_10 : reg n27 a0 = p0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_10]
  have g27_11 : reg n27 a1 = BitVec.ofNat 32 (L.toNat - rem.toNat) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_11]
  have g27_12 : reg n27 a2 = op := by rw [u27.regs, upd_ne (by decide) (by decide), g26_12]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = dg := by rw [u27.regs, upd_ne (by decide) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = rootp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = ll := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = sgp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = kp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = sgl := by rw [u27.regs, upd_ne (by decide) (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = tbl := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
  have g27_13 : reg n27 a3 = ol := by
    rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g26_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w26_48]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m27]; exact w26_2c
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m27]; exact w26_30
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m27]; exact w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m27]; exact w26_38
  have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m27]; exact w26_3c
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m27]; exact w26_40
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m27]; exact w26_44
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m27]; exact w26_48
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m27]; exact w26_4c
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m27]; exact w26_50
  have w27_54 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m27]; exact w26_54
  have w27_58 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m27]; exact w26_58
  have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m27]; exact w26_5c
  have w27_60 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m27]; exact w26_60
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m27]; exact w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m27]; exact w26_68
  have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m27]; exact w26_6c
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m27]; exact w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m27]; exact w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m27]; exact w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m27]; exact w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m27]; exact w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m27]; exact w26_84
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m27]; exact w26_88
  have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m27]; exact w26_8c
  have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m27]; exact w26_90
  have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m27]; exact w26_94
  have w27_98 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m27]; exact w26_98
  have w27_9c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m27]; exact w26_9c
  have w27_a0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m27]; exact w26_a0
  have w27_a4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m27]; exact w26_a4
  have w27_150 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m27]; exact w26_150
  have w27_154 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m27]; exact w26_154
  have w27_158 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m27]; exact w26_158
  have w27_15c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m27]; exact w26_15c
  have w27_408 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m27]; exact w26_408
  have w27_40c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m27]; exact w26_40c
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m27]; exact w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m27]; exact w26_424
  clear w26_424 w26_420 w26_40c w26_408 w26_15c w26_158 w26_154 w26_150 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 w26_2c g26_12 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_11 g26_10 g26_9 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0x490: sv_loF
  obtain ⟨n28, c28, s28, sp28, rk28, R28, K28, fr28⟩ := sv_loF (nl := L.toNat - rem.toNat) (ql := ol.toNat)
    F E27 s27 sv_at_490 sv_at_494 (by decide) (by decide) g27_2
    g27_10 g27_11 g27_12 (by rw [g27_13, ofNat_toNat_self]) ea_in oid_in
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keepL K28 (by decide)
  rw [listsOidOf, listsOidLoop_congr _ _ _ (sv_pt fR27 ea_in), sv_mb fR27 oid_in, ← listsOidOf] at R28
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk28 (3 : Fin 32) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk28 (4 : Fin 32) (by decide), g27_4]
  have g28_9 : reg n28 (9 : Fin 32) = tbp := by rw [rk28 (9 : Fin 32) (by decide), g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rk28 (18 : Fin 32) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rk28 (19 : Fin 32) (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = dg := by rw [rk28 (20 : Fin 32) (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = rootp := by rw [rk28 (21 : Fin 32) (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = ll := by rw [rk28 (22 : Fin 32) (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = sgp := by rw [rk28 (23 : Fin 32) (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = kp := by rw [rk28 (24 : Fin 32) (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = sgl := by rw [rk28 (25 : Fin 32) (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk28 (26 : Fin 32) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = tbl := by rw [rk28 (27 : Fin 32) (by decide), g27_27]
  have g28_2 : reg n28 sp = B + 0x21A0 := sp28
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4)] := keep_kk27.trans K28
  clear keep_kk27
  have w28_2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K28.w32 (by decide) (by decide)).trans w27_2c
  have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K28.w32 (by decide) (by decide)).trans w27_30
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := (K28.w32 (by decide) (by decide)).trans w27_34
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := (K28.w32 (by decide) (by decide)).trans w27_38
  have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K28.w32 (by decide) (by decide)).trans w27_3c
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K28.w32 (by decide) (by decide)).trans w27_40
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := (K28.w32 (by decide) (by decide)).trans w27_44
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K28.w32 (by decide) (by decide)).trans w27_48
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K28.w32 (by decide) (by decide)).trans w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K28.w32 (by decide) (by decide)).trans w27_50
  have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K28.w32 (by decide) (by decide)).trans w27_54
  have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K28.w32 (by decide) (by decide)).trans w27_58
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K28.w32 (by decide) (by decide)).trans w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K28.w32 (by decide) (by decide)).trans w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K28.w32 (by decide) (by decide)).trans w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K28.w32 (by decide) (by decide)).trans w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K28.w32 (by decide) (by decide)).trans w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K28.w32 (by decide) (by decide)).trans w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K28.w32 (by decide) (by decide)).trans w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K28.w32 (by decide) (by decide)).trans w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K28.w32 (by decide) (by decide)).trans w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K28.w32 (by decide) (by decide)).trans w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K28.w32 (by decide) (by decide)).trans w27_84
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K28.w32 (by decide) (by decide)).trans w27_88
  have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K28.w32 (by decide) (by decide)).trans w27_8c
  have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K28.w32 (by decide) (by decide)).trans w27_90
  have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K28.w32 (by decide) (by decide)).trans w27_94
  have w28_98 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K28.w32 (by decide) (by decide)).trans w27_98
  have w28_9c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K28.w32 (by decide) (by decide)).trans w27_9c
  have w28_a0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K28.w32 (by decide) (by decide)).trans w27_a0
  have w28_a4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K28.w32 (by decide) (by decide)).trans w27_a4
  have w28_150 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K28.w32 (by decide) (by decide)).trans w27_150
  have w28_154 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K28.w32 (by decide) (by decide)).trans w27_154
  have w28_158 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K28.w32 (by decide) (by decide)).trans w27_158
  have w28_15c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K28.w32 (by decide) (by decide)).trans w27_15c
  have w28_408 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := (K28.w32 (by decide) (by decide)).trans w27_408
  have w28_40c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := (K28.w32 (by decide) (by decide)).trans w27_40c
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := (K28.w32 (by decide) (by decide)).trans w27_420
  have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := (K28.w32 (by decide) (by decide)).trans w27_424
  clear w27_424 w27_420 w27_40c w27_408 w27_15c w27_158 w27_154 w27_150 w27_a4 w27_a0 w27_9c w27_98 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_44 w27_40 w27_3c w27_38 w27_34 w27_30 w27_2c g27_13 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_12 g27_11 g27_10 g27_9 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  obtain ⟨r28, hr28⟩ : ∃ r, listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op ol.toNat) = r := ⟨_, rfl⟩
  rcases r28 with lb28 | (_ | _)
  · rw [hr28] at R28
    obtain ⟨a0_28, a1_28⟩ := R28
    have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x1 := a0_28
    have g28_11 : reg n28 a1 = (lb28).zeroExtend 32 := a1_28
    -- 0x498
    obtain ⟨n29, c29, u29⟩ := s28.block svX2c498 E28.self svX2c498_end
      ⟨trivial, trivial⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have s29 : St n29.mem SV n29 0x49A (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have rb29 : ∀ q, reg n29 q = (runBlock svX2c498 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
    have g29_9 : reg n29 (9 : Fin 32) = tbp := by
      rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
    have g29_11 : reg n29 a1 = (lb28).zeroExtend 32 := by
      rw [rb29, runBlock_reg _ _ _ a1 s28.zero (by decide), g28_11]
    have g29_18 : reg n29 (18 : Fin 32) = out := by
      rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by
      rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = dg := by
      rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = rootp := by
      rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = ll := by
      rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = sgp := by
      rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = kp := by
      rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = sgl := by
      rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = tbl := by
      rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
    have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb29]; simp +decide only [runBlock, BInstr.run, svX2c498, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g28_2, g28_3, g28_4, g28_9, g28_10, g28_11, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m29]; exact w28_2c
    have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m29]; exact w28_30
    have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m29]; exact w28_34
    have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m29]; exact w28_38
    have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m29]; exact w28_3c
    have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m29]; exact w28_40
    have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m29]; exact w28_44
    have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m29]; exact w28_48
    have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m29]; exact w28_4c
    have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m29]; exact w28_50
    have w29_54 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m29]; exact w28_54
    have w29_58 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m29]; exact w28_58
    have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m29]; exact w28_5c
    have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m29]; exact w28_60
    have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m29]; exact w28_64
    have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m29]; exact w28_68
    have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m29]; exact w28_6c
    have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m29]; exact w28_70
    have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m29]; exact w28_74
    have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m29]; exact w28_78
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m29]; exact w28_7c
    have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m29]; exact w28_80
    have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m29]; exact w28_84
    have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m29]; exact w28_88
    have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m29]; exact w28_8c
    have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m29]; exact w28_90
    have w29_94 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m29]; exact w28_94
    have w29_98 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m29]; exact w28_98
    have w29_9c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m29]; exact w28_9c
    have w29_a0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m29]; exact w28_a0
    have w29_a4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m29]; exact w28_a4
    have w29_150 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m29]; exact w28_150
    have w29_154 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m29]; exact w28_154
    have w29_158 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m29]; exact w28_158
    have w29_15c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m29]; exact w28_15c
    have w29_408 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m29]; exact w28_408
    have w29_40c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m29]; exact w28_40c
    have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m29]; exact w28_420
    have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m29]; exact w28_424
    clear w28_424 w28_420 w28_40c w28_408 w28_15c w28_158 w28_154 w28_150 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 w28_2c g28_2 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_4 g28_3 V28 E28 fR28 t28 fr28 K28 rk28 sp28 s28 c28
    -- 0x49A: sw
    obtain ⟨n30, d30, s30, fr30, K30, W30, rg30⟩ := sv_sw F E29 s29 sv_at_49a (off' := 0x49C) (c := 0x44)
      (by decide) (by rw [g29_2]; sv_addr) (by decide) (by decide)
    have t30 : Steps n0 n30 := t29.trans d30
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.keep K30 (by decide)
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rg30 sp, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg30 (3 : Fin 32), g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg30 (4 : Fin 32), g29_4]
    have g30_9 : reg n30 (9 : Fin 32) = tbp := by rw [rg30 (9 : Fin 32), g29_9]
    have g30_10 : reg n30 a0 = BitVec.ofNat 32 0x1 := by rw [rg30 a0, g29_10]
    have g30_11 : reg n30 a1 = (lb28).zeroExtend 32 := by rw [rg30 a1, g29_11]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rg30 (18 : Fin 32), g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rg30 (19 : Fin 32), g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = dg := by rw [rg30 (20 : Fin 32), g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = rootp := by rw [rg30 (21 : Fin 32), g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = ll := by rw [rg30 (22 : Fin 32), g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = sgp := by rw [rg30 (23 : Fin 32), g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = kp := by rw [rg30 (24 : Fin 32), g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = sgl := by rw [rg30 (25 : Fin 32), g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg30 (26 : Fin 32), g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = tbl := by rw [rg30 (27 : Fin 32), g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := keep_kk29.trans K30.toL
    clear keep_kk29
    have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K30.w32 (by decide) (by decide)).trans w29_2c
    have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K30.w32 (by decide) (by decide)).trans w29_30
    have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := (K30.w32 (by decide) (by decide)).trans w29_34
    have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := (K30.w32 (by decide) (by decide)).trans w29_38
    have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K30.w32 (by decide) (by decide)).trans w29_3c
    have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K30.w32 (by decide) (by decide)).trans w29_40
    have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K30.w32 (by decide) (by decide)).trans w29_48
    have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K30.w32 (by decide) (by decide)).trans w29_4c
    have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K30.w32 (by decide) (by decide)).trans w29_50
    have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K30.w32 (by decide) (by decide)).trans w29_54
    have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K30.w32 (by decide) (by decide)).trans w29_58
    have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K30.w32 (by decide) (by decide)).trans w29_5c
    have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K30.w32 (by decide) (by decide)).trans w29_60
    have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K30.w32 (by decide) (by decide)).trans w29_64
    have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K30.w32 (by decide) (by decide)).trans w29_68
    have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K30.w32 (by decide) (by decide)).trans w29_6c
    have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K30.w32 (by decide) (by decide)).trans w29_70
    have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K30.w32 (by decide) (by decide)).trans w29_74
    have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K30.w32 (by decide) (by decide)).trans w29_78
    have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K30.w32 (by decide) (by decide)).trans w29_7c
    have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K30.w32 (by decide) (by decide)).trans w29_80
    have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K30.w32 (by decide) (by decide)).trans w29_84
    have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K30.w32 (by decide) (by decide)).trans w29_88
    have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K30.w32 (by decide) (by decide)).trans w29_8c
    have w30_90 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K30.w32 (by decide) (by decide)).trans w29_90
    have w30_94 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K30.w32 (by decide) (by decide)).trans w29_94
    have w30_98 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K30.w32 (by decide) (by decide)).trans w29_98
    have w30_9c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K30.w32 (by decide) (by decide)).trans w29_9c
    have w30_a0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K30.w32 (by decide) (by decide)).trans w29_a0
    have w30_a4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K30.w32 (by decide) (by decide)).trans w29_a4
    have w30_150 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K30.w32 (by decide) (by decide)).trans w29_150
    have w30_154 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K30.w32 (by decide) (by decide)).trans w29_154
    have w30_158 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K30.w32 (by decide) (by decide)).trans w29_158
    have w30_15c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K30.w32 (by decide) (by decide)).trans w29_15c
    have w30_408 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := (K30.w32 (by decide) (by decide)).trans w29_408
    have w30_40c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := (K30.w32 (by decide) (by decide)).trans w29_40c
    have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := (K30.w32 (by decide) (by decide)).trans w29_420
    have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := (K30.w32 (by decide) (by decide)).trans w29_424
    have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (lb28).zeroExtend 32 := by rw [W30, g29_11]
    clear w29_424 w29_420 w29_40c w29_408 w29_15c w29_158 w29_154 w29_150 w29_a4 w29_a0 w29_9c w29_98 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_44 w29_40 w29_3c w29_38 w29_34 w29_30 w29_2c g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_9 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29 g28_11 g28_10 a1_28 a0_28
    -- 0x49C: branch, taken
    obtain ⟨n31, d31, u31⟩ := s30.taken E30.self 0x944 sv_at_49c
      (by decide) (by rw [g30_10, s30.zero]; decide)
    have s31 : St n31.mem SV n31 0x944 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, g30_4]
    have g31_9 : reg n31 (9 : Fin 32) = tbp := by rw [u31.regs, g30_9]
    have g31_10 : reg n31 a0 = BitVec.ofNat 32 0x1 := by rw [u31.regs, g30_10]
    have g31_11 : reg n31 a1 = (lb28).zeroExtend 32 := by rw [u31.regs, g30_11]
    have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = dg := by rw [u31.regs, g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = rootp := by rw [u31.regs, g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = ll := by rw [u31.regs, g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = sgp := by rw [u31.regs, g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = kp := by rw [u31.regs, g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = sgl := by rw [u31.regs, g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u31.regs, g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = tbl := by rw [u31.regs, g30_27]
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m31]; exact w30_2c
    have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m31]; exact w30_30
    have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m31]; exact w30_34
    have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m31]; exact w30_38
    have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m31]; exact w30_3c
    have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m31]; exact w30_40
    have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (lb28).zeroExtend 32 := by rw [m31]; exact w30_44
    have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m31]; exact w30_48
    have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m31]; exact w30_4c
    have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m31]; exact w30_50
    have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m31]; exact w30_54
    have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m31]; exact w30_58
    have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m31]; exact w30_5c
    have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m31]; exact w30_60
    have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m31]; exact w30_64
    have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m31]; exact w30_68
    have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m31]; exact w30_6c
    have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m31]; exact w30_70
    have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m31]; exact w30_74
    have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m31]; exact w30_78
    have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m31]; exact w30_7c
    have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m31]; exact w30_80
    have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m31]; exact w30_84
    have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m31]; exact w30_88
    have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m31]; exact w30_8c
    have w31_90 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m31]; exact w30_90
    have w31_94 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m31]; exact w30_94
    have w31_98 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m31]; exact w30_98
    have w31_9c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m31]; exact w30_9c
    have w31_a0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m31]; exact w30_a0
    have w31_a4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m31]; exact w30_a4
    have w31_150 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m31]; exact w30_150
    have w31_154 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m31]; exact w30_154
    have w31_158 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m31]; exact w30_158
    have w31_15c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m31]; exact w30_15c
    have w31_408 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m31]; exact w30_408
    have w31_40c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m31]; exact w30_40c
    have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m31]; exact w30_420
    have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m31]; exact w30_424
    clear w30_44 w30_424 w30_420 w30_40c w30_408 w30_15c w30_158 w30_154 w30_150 w30_a4 w30_a0 w30_9c w30_98 w30_94 w30_90 w30_8c w30_88 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_48 w30_40 w30_3c w30_38 w30_34 w30_30 w30_2c g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_11 g30_10 g30_9 g30_4 g30_3 g30_2 V30 E30 fR30 t30 rg30 W30 K30 fr30 s30 d30
    -- 0x944: lw
    obtain ⟨n32, d32, u32⟩ := s31.lw E31.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g31_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s32 : St n32.mem SV n32 0x946 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
    have g32_9 : reg n32 (9 : Fin 32) = tbp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
    have g32_10 : reg n32 a0 = BitVec.ofNat 32 0x1 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_10]
    have g32_11 : reg n32 a1 = (lb28).zeroExtend 32 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_11]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, upd_ne (by decide) (by decide), g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = sgp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = kp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = sgl := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = tbl := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m32]; exact w31_2c
    have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m32]; exact w31_30
    have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m32]; exact w31_34
    have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m32]; exact w31_38
    have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m32]; exact w31_3c
    have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m32]; exact w31_40
    have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (lb28).zeroExtend 32 := by rw [m32]; exact w31_44
    have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m32]; exact w31_48
    have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m32]; exact w31_4c
    have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m32]; exact w31_50
    have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m32]; exact w31_54
    have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m32]; exact w31_58
    have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m32]; exact w31_5c
    have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m32]; exact w31_60
    have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m32]; exact w31_64
    have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m32]; exact w31_68
    have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m32]; exact w31_6c
    have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m32]; exact w31_70
    have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m32]; exact w31_74
    have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m32]; exact w31_78
    have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m32]; exact w31_7c
    have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m32]; exact w31_80
    have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m32]; exact w31_84
    have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m32]; exact w31_88
    have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m32]; exact w31_8c
    have w32_90 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m32]; exact w31_90
    have w32_94 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m32]; exact w31_94
    have w32_98 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m32]; exact w31_98
    have w32_9c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m32]; exact w31_9c
    have w32_a0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m32]; exact w31_a0
    have w32_a4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m32]; exact w31_a4
    have w32_150 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m32]; exact w31_150
    have w32_154 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m32]; exact w31_154
    have w32_158 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m32]; exact w31_158
    have w32_15c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m32]; exact w31_15c
    have w32_408 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m32]; exact w31_408
    have w32_40c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m32]; exact w31_40c
    have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m32]; exact w31_420
    have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m32]; exact w31_424
    clear w31_424 w31_420 w31_40c w31_408 w31_15c w31_158 w31_154 w31_150 w31_a4 w31_a0 w31_9c w31_98 w31_94 w31_90 w31_8c w31_88 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_48 w31_44 w31_40 w31_3c w31_38 w31_34 w31_30 w31_2c g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_11 g31_10 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    -- 0x946: j
    obtain ⟨n33, d33, u33⟩ := s32.jump E32.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s32.pc]; decide)
    have s33 : St n33.mem SV n33 0x7A4 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
    have m33 : n33.mem = n32.mem := u33.mem
    have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
    have t33 : Steps n0 n33 := t32.trans (.single d33)
    have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
    have E33 : SvCode n33.mem := E32.fr F fr33
    have V33 : SvSaves B n33.mem v := V32.same m33
    have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
    have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
    have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
    have g33_9 : reg n33 (9 : Fin 32) = tbp := by rw [u33.regs, g32_9]
    have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x1 := by rw [u33.regs, g32_10]
    have g33_11 : reg n33 a1 = (lb28).zeroExtend 32 := by rw [u33.regs, g32_11]
    have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
    have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
    have g33_20 : reg n33 (20 : Fin 32) = dg := by rw [u33.regs, g32_20]
    have g33_21 : reg n33 (21 : Fin 32) = rootp := by rw [u33.regs, g32_21]
    have g33_22 : reg n33 (22 : Fin 32) = ll := by rw [u33.regs, g32_22]
    have g33_23 : reg n33 (23 : Fin 32) = sgp := by rw [u33.regs, g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = kp := by rw [u33.regs, g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = sgl := by rw [u33.regs, g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u33.regs, g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = tbl := by rw [u33.regs, g32_27]
    have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := by rw [m33]; exact keep_kk32
    clear keep_kk32
    have w33_2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m33]; exact w32_2c
    have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m33]; exact w32_30
    have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m33]; exact w32_34
    have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m33]; exact w32_38
    have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m33]; exact w32_3c
    have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m33]; exact w32_40
    have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (lb28).zeroExtend 32 := by rw [m33]; exact w32_44
    have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m33]; exact w32_48
    have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m33]; exact w32_4c
    have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m33]; exact w32_50
    have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m33]; exact w32_54
    have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m33]; exact w32_58
    have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m33]; exact w32_5c
    have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m33]; exact w32_60
    have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m33]; exact w32_64
    have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m33]; exact w32_68
    have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m33]; exact w32_6c
    have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m33]; exact w32_70
    have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m33]; exact w32_74
    have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m33]; exact w32_78
    have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m33]; exact w32_7c
    have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m33]; exact w32_80
    have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m33]; exact w32_84
    have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m33]; exact w32_88
    have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m33]; exact w32_8c
    have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m33]; exact w32_90
    have w33_94 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m33]; exact w32_94
    have w33_98 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m33]; exact w32_98
    have w33_9c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m33]; exact w32_9c
    have w33_a0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m33]; exact w32_a0
    have w33_a4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m33]; exact w32_a4
    have w33_150 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m33]; exact w32_150
    have w33_154 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m33]; exact w32_154
    have w33_158 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m33]; exact w32_158
    have w33_15c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m33]; exact w32_15c
    have w33_408 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m33]; exact w32_408
    have w33_40c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m33]; exact w32_40c
    have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m33]; exact w32_420
    have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m33]; exact w32_424
    clear w32_424 w32_420 w32_40c w32_408 w32_15c w32_158 w32_154 w32_150 w32_a4 w32_a0 w32_9c w32_98 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_48 w32_44 w32_40 w32_3c w32_38 w32_34 w32_30 w32_2c g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_10 g32_9 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
    exact .inl ⟨(fun ⟨h0', tb7', h1', vp14', vl14', h2', te14', h3', h4', h5', _⟩ => by rw [hr7] at h0'; cases h0'; rw [htb7] at h1'; cases h1'; rw [hr14] at h2'; cases h2'; rw [ht14] at h3'; cases h3'; rw [hr28] at h5'; cases h5'), sv_fail F E33 s33 t33 (fun x hx => (fR33 x hx).trans (fM x hx).symm) V33 hret g33_2 g33_18 hO g33_3 g33_4⟩
  rotate_left
  · rw [hr28] at R28
    obtain ⟨a0_28, a1_28⟩ := R28
    have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x0 := a0_28
    have g28_11 : reg n28 a1 = BitVec.ofNat 32 0x1 := by rw [a1_28]; rfl
    -- 0x498
    obtain ⟨n29, c29, u29⟩ := s28.block svX2c498 E28.self svX2c498_end
      ⟨trivial, trivial⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have s29 : St n29.mem SV n29 0x49A (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have rb29 : ∀ q, reg n29 q = (runBlock svX2c498 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
    have g29_9 : reg n29 (9 : Fin 32) = tbp := by
      rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
    have g29_11 : reg n29 a1 = BitVec.ofNat 32 0x1 := by
      rw [rb29, runBlock_reg _ _ _ a1 s28.zero (by decide), g28_11]
    have g29_18 : reg n29 (18 : Fin 32) = out := by
      rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by
      rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = dg := by
      rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = rootp := by
      rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = ll := by
      rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = sgp := by
      rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = kp := by
      rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = sgl := by
      rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = tbl := by
      rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
    have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb29]; simp +decide only [runBlock, BInstr.run, svX2c498, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g28_2, g28_3, g28_4, g28_9, g28_10, g28_11, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m29]; exact w28_2c
    have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m29]; exact w28_30
    have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m29]; exact w28_34
    have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m29]; exact w28_38
    have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m29]; exact w28_3c
    have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m29]; exact w28_40
    have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m29]; exact w28_44
    have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m29]; exact w28_48
    have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m29]; exact w28_4c
    have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m29]; exact w28_50
    have w29_54 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m29]; exact w28_54
    have w29_58 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m29]; exact w28_58
    have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m29]; exact w28_5c
    have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m29]; exact w28_60
    have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m29]; exact w28_64
    have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m29]; exact w28_68
    have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m29]; exact w28_6c
    have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m29]; exact w28_70
    have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m29]; exact w28_74
    have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m29]; exact w28_78
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m29]; exact w28_7c
    have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m29]; exact w28_80
    have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m29]; exact w28_84
    have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m29]; exact w28_88
    have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m29]; exact w28_8c
    have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m29]; exact w28_90
    have w29_94 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m29]; exact w28_94
    have w29_98 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m29]; exact w28_98
    have w29_9c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m29]; exact w28_9c
    have w29_a0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m29]; exact w28_a0
    have w29_a4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m29]; exact w28_a4
    have w29_150 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m29]; exact w28_150
    have w29_154 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m29]; exact w28_154
    have w29_158 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m29]; exact w28_158
    have w29_15c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m29]; exact w28_15c
    have w29_408 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m29]; exact w28_408
    have w29_40c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m29]; exact w28_40c
    have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m29]; exact w28_420
    have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m29]; exact w28_424
    clear w28_424 w28_420 w28_40c w28_408 w28_15c w28_158 w28_154 w28_150 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 w28_2c g28_2 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_4 g28_3 V28 E28 fR28 t28 fr28 K28 rk28 sp28 s28 c28
    -- 0x49A: sw
    obtain ⟨n30, d30, s30, fr30, K30, W30, rg30⟩ := sv_sw F E29 s29 sv_at_49a (off' := 0x49C) (c := 0x44)
      (by decide) (by rw [g29_2]; sv_addr) (by decide) (by decide)
    have t30 : Steps n0 n30 := t29.trans d30
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.keep K30 (by decide)
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rg30 sp, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg30 (3 : Fin 32), g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg30 (4 : Fin 32), g29_4]
    have g30_9 : reg n30 (9 : Fin 32) = tbp := by rw [rg30 (9 : Fin 32), g29_9]
    have g30_10 : reg n30 a0 = BitVec.ofNat 32 0x0 := by rw [rg30 a0, g29_10]
    have g30_11 : reg n30 a1 = BitVec.ofNat 32 0x1 := by rw [rg30 a1, g29_11]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rg30 (18 : Fin 32), g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rg30 (19 : Fin 32), g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = dg := by rw [rg30 (20 : Fin 32), g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = rootp := by rw [rg30 (21 : Fin 32), g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = ll := by rw [rg30 (22 : Fin 32), g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = sgp := by rw [rg30 (23 : Fin 32), g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = kp := by rw [rg30 (24 : Fin 32), g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = sgl := by rw [rg30 (25 : Fin 32), g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg30 (26 : Fin 32), g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = tbl := by rw [rg30 (27 : Fin 32), g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := keep_kk29.trans K30.toL
    clear keep_kk29
    have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K30.w32 (by decide) (by decide)).trans w29_2c
    have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K30.w32 (by decide) (by decide)).trans w29_30
    have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := (K30.w32 (by decide) (by decide)).trans w29_34
    have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := (K30.w32 (by decide) (by decide)).trans w29_38
    have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K30.w32 (by decide) (by decide)).trans w29_3c
    have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K30.w32 (by decide) (by decide)).trans w29_40
    have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K30.w32 (by decide) (by decide)).trans w29_48
    have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K30.w32 (by decide) (by decide)).trans w29_4c
    have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K30.w32 (by decide) (by decide)).trans w29_50
    have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K30.w32 (by decide) (by decide)).trans w29_54
    have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K30.w32 (by decide) (by decide)).trans w29_58
    have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K30.w32 (by decide) (by decide)).trans w29_5c
    have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K30.w32 (by decide) (by decide)).trans w29_60
    have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K30.w32 (by decide) (by decide)).trans w29_64
    have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K30.w32 (by decide) (by decide)).trans w29_68
    have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K30.w32 (by decide) (by decide)).trans w29_6c
    have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K30.w32 (by decide) (by decide)).trans w29_70
    have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K30.w32 (by decide) (by decide)).trans w29_74
    have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K30.w32 (by decide) (by decide)).trans w29_78
    have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K30.w32 (by decide) (by decide)).trans w29_7c
    have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K30.w32 (by decide) (by decide)).trans w29_80
    have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K30.w32 (by decide) (by decide)).trans w29_84
    have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K30.w32 (by decide) (by decide)).trans w29_88
    have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K30.w32 (by decide) (by decide)).trans w29_8c
    have w30_90 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K30.w32 (by decide) (by decide)).trans w29_90
    have w30_94 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K30.w32 (by decide) (by decide)).trans w29_94
    have w30_98 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K30.w32 (by decide) (by decide)).trans w29_98
    have w30_9c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K30.w32 (by decide) (by decide)).trans w29_9c
    have w30_a0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K30.w32 (by decide) (by decide)).trans w29_a0
    have w30_a4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K30.w32 (by decide) (by decide)).trans w29_a4
    have w30_150 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K30.w32 (by decide) (by decide)).trans w29_150
    have w30_154 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K30.w32 (by decide) (by decide)).trans w29_154
    have w30_158 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K30.w32 (by decide) (by decide)).trans w29_158
    have w30_15c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K30.w32 (by decide) (by decide)).trans w29_15c
    have w30_408 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := (K30.w32 (by decide) (by decide)).trans w29_408
    have w30_40c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := (K30.w32 (by decide) (by decide)).trans w29_40c
    have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := (K30.w32 (by decide) (by decide)).trans w29_420
    have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := (K30.w32 (by decide) (by decide)).trans w29_424
    have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [W30, g29_11]
    clear w29_424 w29_420 w29_40c w29_408 w29_15c w29_158 w29_154 w29_150 w29_a4 w29_a0 w29_9c w29_98 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_44 w29_40 w29_3c w29_38 w29_34 w29_30 w29_2c g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_9 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29 g28_11 g28_10 a1_28 a0_28
    -- 0x49C: branch, not taken
    obtain ⟨n31, d31, u31⟩ := s30.notTaken E30.self 0x4A0 sv_at_49c
      (by decide) (by rw [g30_10, s30.zero]; decide)
    have s31 : St n31.mem SV n31 0x4A0 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, g30_4]
    have g31_9 : reg n31 (9 : Fin 32) = tbp := by rw [u31.regs, g30_9]
    have g31_10 : reg n31 a0 = BitVec.ofNat 32 0x0 := by rw [u31.regs, g30_10]
    have g31_11 : reg n31 a1 = BitVec.ofNat 32 0x1 := by rw [u31.regs, g30_11]
    have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = dg := by rw [u31.regs, g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = rootp := by rw [u31.regs, g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = ll := by rw [u31.regs, g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = sgp := by rw [u31.regs, g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = kp := by rw [u31.regs, g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = sgl := by rw [u31.regs, g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u31.regs, g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = tbl := by rw [u31.regs, g30_27]
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m31]; exact w30_2c
    have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m31]; exact w30_30
    have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m31]; exact w30_34
    have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m31]; exact w30_38
    have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m31]; exact w30_3c
    have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m31]; exact w30_40
    have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m31]; exact w30_44
    have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m31]; exact w30_48
    have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m31]; exact w30_4c
    have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m31]; exact w30_50
    have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m31]; exact w30_54
    have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m31]; exact w30_58
    have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m31]; exact w30_5c
    have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m31]; exact w30_60
    have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m31]; exact w30_64
    have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m31]; exact w30_68
    have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m31]; exact w30_6c
    have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m31]; exact w30_70
    have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m31]; exact w30_74
    have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m31]; exact w30_78
    have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m31]; exact w30_7c
    have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m31]; exact w30_80
    have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m31]; exact w30_84
    have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m31]; exact w30_88
    have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m31]; exact w30_8c
    have w31_90 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m31]; exact w30_90
    have w31_94 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m31]; exact w30_94
    have w31_98 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m31]; exact w30_98
    have w31_9c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m31]; exact w30_9c
    have w31_a0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m31]; exact w30_a0
    have w31_a4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m31]; exact w30_a4
    have w31_150 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m31]; exact w30_150
    have w31_154 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m31]; exact w30_154
    have w31_158 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m31]; exact w30_158
    have w31_15c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m31]; exact w30_15c
    have w31_408 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m31]; exact w30_408
    have w31_40c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m31]; exact w30_40c
    have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m31]; exact w30_420
    have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m31]; exact w30_424
    clear w30_44 w30_424 w30_420 w30_40c w30_408 w30_15c w30_158 w30_154 w30_150 w30_a4 w30_a0 w30_9c w30_98 w30_94 w30_90 w30_8c w30_88 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_48 w30_40 w30_3c w30_38 w30_34 w30_30 w30_2c g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_11 g30_10 g30_9 g30_4 g30_3 g30_2 V30 E30 fR30 t30 rg30 W30 K30 fr30 s30 d30
    -- 0x4A0: lw
    obtain ⟨n32, d32, u32⟩ := s31.lw E31.self sv_at_4a0 (off' := 0x4A2) (by decide)
      (by rw [g31_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s32 : St n32.mem SV n32 0x4A2 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
    have g32_9 : reg n32 (9 : Fin 32) = tbp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
    have g32_11 : reg n32 a1 = BitVec.ofNat 32 0x1 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_11]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, upd_ne (by decide) (by decide), g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = sgp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = kp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = sgl := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = tbl := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
    have g32_10 : reg n32 a0 = BitVec.ofNat 32 0x1 := by
      rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g31_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w31_44]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m32]; exact w31_2c
    have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m32]; exact w31_30
    have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m32]; exact w31_34
    have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m32]; exact w31_38
    have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m32]; exact w31_3c
    have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m32]; exact w31_40
    have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m32]; exact w31_44
    have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m32]; exact w31_48
    have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m32]; exact w31_4c
    have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m32]; exact w31_50
    have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m32]; exact w31_54
    have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m32]; exact w31_58
    have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m32]; exact w31_5c
    have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m32]; exact w31_60
    have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m32]; exact w31_64
    have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m32]; exact w31_68
    have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m32]; exact w31_6c
    have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m32]; exact w31_70
    have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m32]; exact w31_74
    have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m32]; exact w31_78
    have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m32]; exact w31_7c
    have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m32]; exact w31_80
    have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m32]; exact w31_84
    have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m32]; exact w31_88
    have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m32]; exact w31_8c
    have w32_90 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m32]; exact w31_90
    have w32_94 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m32]; exact w31_94
    have w32_98 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m32]; exact w31_98
    have w32_9c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m32]; exact w31_9c
    have w32_a0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m32]; exact w31_a0
    have w32_a4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m32]; exact w31_a4
    have w32_150 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m32]; exact w31_150
    have w32_154 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m32]; exact w31_154
    have w32_158 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m32]; exact w31_158
    have w32_15c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m32]; exact w31_15c
    have w32_408 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m32]; exact w31_408
    have w32_40c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m32]; exact w31_40c
    have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m32]; exact w31_420
    have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m32]; exact w31_424
    clear w31_424 w31_420 w31_40c w31_408 w31_15c w31_158 w31_154 w31_150 w31_a4 w31_a0 w31_9c w31_98 w31_94 w31_90 w31_8c w31_88 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_48 w31_44 w31_40 w31_3c w31_38 w31_34 w31_30 w31_2c g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_11 g31_10 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    -- 0x4A2
    obtain ⟨n33, c33, u33⟩ := s32.block svX2c4a2 E32.self svX2c4a2_end
      ⟨trivial, trivial, trivial⟩
    have m33 : n33.mem = n32.mem := u33.mem
    have s33 : St n33.mem SV n33 0x4A6 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
    have rb33 : ∀ q, reg n33 q = (runBlock svX2c4a2 (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
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
    have g33_9 : reg n33 (9 : Fin 32) = tbp := by
      rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
    have g33_18 : reg n33 (18 : Fin 32) = out := by
      rw [rb33, runBlock_reg _ _ _ (18 : Fin 32) s32.zero (by decide), g32_18]
    have g33_19 : reg n33 (19 : Fin 32) = bp := by
      rw [rb33, runBlock_reg _ _ _ (19 : Fin 32) s32.zero (by decide), g32_19]
    have g33_20 : reg n33 (20 : Fin 32) = dg := by
      rw [rb33, runBlock_reg _ _ _ (20 : Fin 32) s32.zero (by decide), g32_20]
    have g33_21 : reg n33 (21 : Fin 32) = rootp := by
      rw [rb33, runBlock_reg _ _ _ (21 : Fin 32) s32.zero (by decide), g32_21]
    have g33_22 : reg n33 (22 : Fin 32) = ll := by
      rw [rb33, runBlock_reg _ _ _ (22 : Fin 32) s32.zero (by decide), g32_22]
    have g33_23 : reg n33 (23 : Fin 32) = sgp := by
      rw [rb33, runBlock_reg _ _ _ (23 : Fin 32) s32.zero (by decide), g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = kp := by
      rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = sgl := by
      rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = tbl := by
      rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
    have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb33]; simp +decide only [runBlock, BInstr.run, svX2c4a2, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g32_2, g32_3, g32_4, g32_9, g32_10, g32_11, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g33_11 : reg n33 a1 = BitVec.ofNat 32 0x16 := by
      rw [rb33]; simp +decide only [runBlock, BInstr.run, svX2c4a2, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g32_2, g32_3, g32_4, g32_9, g32_10, g32_11, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := by rw [m33]; exact keep_kk32
    clear keep_kk32
    have w33_2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m33]; exact w32_2c
    have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m33]; exact w32_30
    have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m33]; exact w32_34
    have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m33]; exact w32_38
    have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m33]; exact w32_3c
    have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m33]; exact w32_40
    have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m33]; exact w32_44
    have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m33]; exact w32_48
    have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m33]; exact w32_4c
    have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m33]; exact w32_50
    have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m33]; exact w32_54
    have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m33]; exact w32_58
    have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m33]; exact w32_5c
    have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m33]; exact w32_60
    have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m33]; exact w32_64
    have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m33]; exact w32_68
    have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m33]; exact w32_6c
    have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m33]; exact w32_70
    have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m33]; exact w32_74
    have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m33]; exact w32_78
    have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m33]; exact w32_7c
    have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m33]; exact w32_80
    have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m33]; exact w32_84
    have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m33]; exact w32_88
    have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m33]; exact w32_8c
    have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m33]; exact w32_90
    have w33_94 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m33]; exact w32_94
    have w33_98 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m33]; exact w32_98
    have w33_9c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m33]; exact w32_9c
    have w33_a0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m33]; exact w32_a0
    have w33_a4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m33]; exact w32_a4
    have w33_150 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m33]; exact w32_150
    have w33_154 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m33]; exact w32_154
    have w33_158 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m33]; exact w32_158
    have w33_15c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m33]; exact w32_15c
    have w33_408 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m33]; exact w32_408
    have w33_40c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m33]; exact w32_40c
    have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m33]; exact w32_420
    have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m33]; exact w32_424
    clear w32_424 w32_420 w32_40c w32_408 w32_15c w32_158 w32_154 w32_150 w32_a4 w32_a0 w32_9c w32_98 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_48 w32_44 w32_40 w32_3c w32_38 w32_34 w32_30 w32_2c g32_10 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_9 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
    -- 0x4A6: sw
    obtain ⟨n34, d34, s34, fr34, K34, W34, rg34⟩ := sv_sw F E33 s33 sv_at_4a6 (off' := 0x4A8) (c := 0x44)
      (by decide) (by rw [g33_2]; sv_addr) (by decide) (by decide)
    have t34 : Steps n0 n34 := t33.trans d34
    have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.keep K34 (by decide)
    have g34_2 : reg n34 sp = B + 0x21A0 := by rw [rg34 sp, g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg34 (3 : Fin 32), g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg34 (4 : Fin 32), g33_4]
    have g34_9 : reg n34 (9 : Fin 32) = tbp := by rw [rg34 (9 : Fin 32), g33_9]
    have g34_10 : reg n34 a0 = BitVec.ofNat 32 0x1 := by rw [rg34 a0, g33_10]
    have g34_11 : reg n34 a1 = BitVec.ofNat 32 0x16 := by rw [rg34 a1, g33_11]
    have g34_18 : reg n34 (18 : Fin 32) = out := by rw [rg34 (18 : Fin 32), g33_18]
    have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [rg34 (19 : Fin 32), g33_19]
    have g34_20 : reg n34 (20 : Fin 32) = dg := by rw [rg34 (20 : Fin 32), g33_20]
    have g34_21 : reg n34 (21 : Fin 32) = rootp := by rw [rg34 (21 : Fin 32), g33_21]
    have g34_22 : reg n34 (22 : Fin 32) = ll := by rw [rg34 (22 : Fin 32), g33_22]
    have g34_23 : reg n34 (23 : Fin 32) = sgp := by rw [rg34 (23 : Fin 32), g33_23]
    have g34_24 : reg n34 (24 : Fin 32) = kp := by rw [rg34 (24 : Fin 32), g33_24]
    have g34_25 : reg n34 (25 : Fin 32) = sgl := by rw [rg34 (25 : Fin 32), g33_25]
    have g34_26 : reg n34 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg34 (26 : Fin 32), g33_26]
    have g34_27 : reg n34 (27 : Fin 32) = tbl := by rw [rg34 (27 : Fin 32), g33_27]
    have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4)] := keep_kk33.trans K34.toL
    clear keep_kk33
    have w34_2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K34.w32 (by decide) (by decide)).trans w33_2c
    have w34_30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K34.w32 (by decide) (by decide)).trans w33_30
    have w34_34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := (K34.w32 (by decide) (by decide)).trans w33_34
    have w34_38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := (K34.w32 (by decide) (by decide)).trans w33_38
    have w34_3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K34.w32 (by decide) (by decide)).trans w33_3c
    have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K34.w32 (by decide) (by decide)).trans w33_40
    have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K34.w32 (by decide) (by decide)).trans w33_48
    have w34_4c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K34.w32 (by decide) (by decide)).trans w33_4c
    have w34_50 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K34.w32 (by decide) (by decide)).trans w33_50
    have w34_54 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K34.w32 (by decide) (by decide)).trans w33_54
    have w34_58 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K34.w32 (by decide) (by decide)).trans w33_58
    have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K34.w32 (by decide) (by decide)).trans w33_5c
    have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K34.w32 (by decide) (by decide)).trans w33_60
    have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K34.w32 (by decide) (by decide)).trans w33_64
    have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K34.w32 (by decide) (by decide)).trans w33_68
    have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K34.w32 (by decide) (by decide)).trans w33_6c
    have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K34.w32 (by decide) (by decide)).trans w33_70
    have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K34.w32 (by decide) (by decide)).trans w33_74
    have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K34.w32 (by decide) (by decide)).trans w33_78
    have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K34.w32 (by decide) (by decide)).trans w33_7c
    have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K34.w32 (by decide) (by decide)).trans w33_80
    have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K34.w32 (by decide) (by decide)).trans w33_84
    have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K34.w32 (by decide) (by decide)).trans w33_88
    have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K34.w32 (by decide) (by decide)).trans w33_8c
    have w34_90 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K34.w32 (by decide) (by decide)).trans w33_90
    have w34_94 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K34.w32 (by decide) (by decide)).trans w33_94
    have w34_98 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K34.w32 (by decide) (by decide)).trans w33_98
    have w34_9c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K34.w32 (by decide) (by decide)).trans w33_9c
    have w34_a0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K34.w32 (by decide) (by decide)).trans w33_a0
    have w34_a4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K34.w32 (by decide) (by decide)).trans w33_a4
    have w34_150 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K34.w32 (by decide) (by decide)).trans w33_150
    have w34_154 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K34.w32 (by decide) (by decide)).trans w33_154
    have w34_158 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K34.w32 (by decide) (by decide)).trans w33_158
    have w34_15c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K34.w32 (by decide) (by decide)).trans w33_15c
    have w34_408 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := (K34.w32 (by decide) (by decide)).trans w33_408
    have w34_40c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := (K34.w32 (by decide) (by decide)).trans w33_40c
    have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := (K34.w32 (by decide) (by decide)).trans w33_420
    have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := (K34.w32 (by decide) (by decide)).trans w33_424
    have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [W34, g33_11]
    clear w33_424 w33_420 w33_40c w33_408 w33_15c w33_158 w33_154 w33_150 w33_a4 w33_a0 w33_9c w33_98 w33_94 w33_90 w33_8c w33_88 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_48 w33_44 w33_40 w33_3c w33_38 w33_34 w33_30 w33_2c g33_11 g33_10 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
    -- 0x4A8: branch, taken
    obtain ⟨n35, d35, u35⟩ := s34.taken E34.self 0x944 sv_at_4a8
      (by decide) (by rw [g34_10, s34.zero]; decide)
    have s35 : St n35.mem SV n35 0x944 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
    have m35 : n35.mem = n34.mem := u35.mem
    have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
    have t35 : Steps n0 n35 := t34.trans (.single d35)
    have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
    have E35 : SvCode n35.mem := E34.fr F fr35
    have V35 : SvSaves B n35.mem v := V34.same m35
    have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, g34_2]
    have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, g34_3]
    have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, g34_4]
    have g35_9 : reg n35 (9 : Fin 32) = tbp := by rw [u35.regs, g34_9]
    have g35_10 : reg n35 a0 = BitVec.ofNat 32 0x1 := by rw [u35.regs, g34_10]
    have g35_11 : reg n35 a1 = BitVec.ofNat 32 0x16 := by rw [u35.regs, g34_11]
    have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
    have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
    have g35_20 : reg n35 (20 : Fin 32) = dg := by rw [u35.regs, g34_20]
    have g35_21 : reg n35 (21 : Fin 32) = rootp := by rw [u35.regs, g34_21]
    have g35_22 : reg n35 (22 : Fin 32) = ll := by rw [u35.regs, g34_22]
    have g35_23 : reg n35 (23 : Fin 32) = sgp := by rw [u35.regs, g34_23]
    have g35_24 : reg n35 (24 : Fin 32) = kp := by rw [u35.regs, g34_24]
    have g35_25 : reg n35 (25 : Fin 32) = sgl := by rw [u35.regs, g34_25]
    have g35_26 : reg n35 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u35.regs, g34_26]
    have g35_27 : reg n35 (27 : Fin 32) = tbl := by rw [u35.regs, g34_27]
    have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4)] := by rw [m35]; exact keep_kk34
    clear keep_kk34
    have w35_2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m35]; exact w34_2c
    have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m35]; exact w34_30
    have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m35]; exact w34_34
    have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m35]; exact w34_38
    have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m35]; exact w34_3c
    have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m35]; exact w34_40
    have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m35]; exact w34_44
    have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m35]; exact w34_48
    have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m35]; exact w34_4c
    have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m35]; exact w34_50
    have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m35]; exact w34_54
    have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m35]; exact w34_58
    have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m35]; exact w34_5c
    have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m35]; exact w34_60
    have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m35]; exact w34_64
    have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m35]; exact w34_68
    have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m35]; exact w34_6c
    have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m35]; exact w34_70
    have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m35]; exact w34_74
    have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m35]; exact w34_78
    have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m35]; exact w34_7c
    have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m35]; exact w34_80
    have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m35]; exact w34_84
    have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m35]; exact w34_88
    have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m35]; exact w34_8c
    have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m35]; exact w34_90
    have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m35]; exact w34_94
    have w35_98 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m35]; exact w34_98
    have w35_9c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m35]; exact w34_9c
    have w35_a0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m35]; exact w34_a0
    have w35_a4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m35]; exact w34_a4
    have w35_150 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m35]; exact w34_150
    have w35_154 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m35]; exact w34_154
    have w35_158 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m35]; exact w34_158
    have w35_15c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m35]; exact w34_15c
    have w35_408 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m35]; exact w34_408
    have w35_40c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m35]; exact w34_40c
    have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m35]; exact w34_420
    have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m35]; exact w34_424
    clear w34_44 w34_424 w34_420 w34_40c w34_408 w34_15c w34_158 w34_154 w34_150 w34_a4 w34_a0 w34_9c w34_98 w34_94 w34_90 w34_8c w34_88 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_40 w34_3c w34_38 w34_34 w34_30 w34_2c g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_11 g34_10 g34_9 g34_4 g34_3 g34_2 V34 E34 fR34 t34 rg34 W34 K34 fr34 s34 d34
    -- 0x944: lw
    obtain ⟨n36, d36, u36⟩ := s35.lw E35.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g35_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s36 : St n36.mem SV n36 0x946 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
    have m36 : n36.mem = n35.mem := u36.mem
    have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
    have t36 : Steps n0 n36 := t35.trans (.single d36)
    have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
    have E36 : SvCode n36.mem := E35.fr F fr36
    have V36 : SvSaves B n36.mem v := V35.same m36
    have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
    have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
    have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
    have g36_9 : reg n36 (9 : Fin 32) = tbp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
    have g36_10 : reg n36 a0 = BitVec.ofNat 32 0x1 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_10]
    have g36_11 : reg n36 a1 = BitVec.ofNat 32 0x16 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_11]
    have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
    have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
    have g36_20 : reg n36 (20 : Fin 32) = dg := by rw [u36.regs, upd_ne (by decide) (by decide), g35_20]
    have g36_21 : reg n36 (21 : Fin 32) = rootp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
    have g36_22 : reg n36 (22 : Fin 32) = ll := by rw [u36.regs, upd_ne (by decide) (by decide), g35_22]
    have g36_23 : reg n36 (23 : Fin 32) = sgp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_23]
    have g36_24 : reg n36 (24 : Fin 32) = kp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_24]
    have g36_25 : reg n36 (25 : Fin 32) = sgl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
    have g36_26 : reg n36 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
    have g36_27 : reg n36 (27 : Fin 32) = tbl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
    have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4)] := by rw [m36]; exact keep_kk35
    clear keep_kk35
    have w36_2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m36]; exact w35_2c
    have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m36]; exact w35_30
    have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m36]; exact w35_34
    have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m36]; exact w35_38
    have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m36]; exact w35_3c
    have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m36]; exact w35_40
    have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m36]; exact w35_44
    have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m36]; exact w35_48
    have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m36]; exact w35_4c
    have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m36]; exact w35_50
    have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m36]; exact w35_54
    have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m36]; exact w35_58
    have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m36]; exact w35_5c
    have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m36]; exact w35_60
    have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m36]; exact w35_64
    have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m36]; exact w35_68
    have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m36]; exact w35_6c
    have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m36]; exact w35_70
    have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m36]; exact w35_74
    have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m36]; exact w35_78
    have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m36]; exact w35_7c
    have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m36]; exact w35_80
    have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m36]; exact w35_84
    have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m36]; exact w35_88
    have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m36]; exact w35_8c
    have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m36]; exact w35_90
    have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m36]; exact w35_94
    have w36_98 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m36]; exact w35_98
    have w36_9c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m36]; exact w35_9c
    have w36_a0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m36]; exact w35_a0
    have w36_a4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m36]; exact w35_a4
    have w36_150 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m36]; exact w35_150
    have w36_154 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m36]; exact w35_154
    have w36_158 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m36]; exact w35_158
    have w36_15c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m36]; exact w35_15c
    have w36_408 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m36]; exact w35_408
    have w36_40c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m36]; exact w35_40c
    have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m36]; exact w35_420
    have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m36]; exact w35_424
    clear w35_424 w35_420 w35_40c w35_408 w35_15c w35_158 w35_154 w35_150 w35_a4 w35_a0 w35_9c w35_98 w35_94 w35_90 w35_8c w35_88 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_44 w35_40 w35_3c w35_38 w35_34 w35_30 w35_2c g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_11 g35_10 g35_9 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
    -- 0x946: j
    obtain ⟨n37, d37, u37⟩ := s36.jump E36.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s36.pc]; decide)
    have s37 : St n37.mem SV n37 0x7A4 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
    have m37 : n37.mem = n36.mem := u37.mem
    have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
    have t37 : Steps n0 n37 := t36.trans (.single d37)
    have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
    have E37 : SvCode n37.mem := E36.fr F fr37
    have V37 : SvSaves B n37.mem v := V36.same m37
    have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
    have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
    have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
    have g37_9 : reg n37 (9 : Fin 32) = tbp := by rw [u37.regs, g36_9]
    have g37_10 : reg n37 a0 = BitVec.ofNat 32 0x1 := by rw [u37.regs, g36_10]
    have g37_11 : reg n37 a1 = BitVec.ofNat 32 0x16 := by rw [u37.regs, g36_11]
    have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
    have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
    have g37_20 : reg n37 (20 : Fin 32) = dg := by rw [u37.regs, g36_20]
    have g37_21 : reg n37 (21 : Fin 32) = rootp := by rw [u37.regs, g36_21]
    have g37_22 : reg n37 (22 : Fin 32) = ll := by rw [u37.regs, g36_22]
    have g37_23 : reg n37 (23 : Fin 32) = sgp := by rw [u37.regs, g36_23]
    have g37_24 : reg n37 (24 : Fin 32) = kp := by rw [u37.regs, g36_24]
    have g37_25 : reg n37 (25 : Fin 32) = sgl := by rw [u37.regs, g36_25]
    have g37_26 : reg n37 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u37.regs, g36_26]
    have g37_27 : reg n37 (27 : Fin 32) = tbl := by rw [u37.regs, g36_27]
    have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4)] := by rw [m37]; exact keep_kk36
    clear keep_kk36
    have w37_2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m37]; exact w36_2c
    have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m37]; exact w36_30
    have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m37]; exact w36_34
    have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m37]; exact w36_38
    have w37_3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m37]; exact w36_3c
    have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m37]; exact w36_40
    have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m37]; exact w36_44
    have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m37]; exact w36_48
    have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m37]; exact w36_4c
    have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m37]; exact w36_50
    have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m37]; exact w36_54
    have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m37]; exact w36_58
    have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m37]; exact w36_5c
    have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m37]; exact w36_60
    have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m37]; exact w36_64
    have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m37]; exact w36_68
    have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m37]; exact w36_6c
    have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m37]; exact w36_70
    have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m37]; exact w36_74
    have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m37]; exact w36_78
    have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m37]; exact w36_7c
    have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m37]; exact w36_80
    have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m37]; exact w36_84
    have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m37]; exact w36_88
    have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m37]; exact w36_8c
    have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m37]; exact w36_90
    have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m37]; exact w36_94
    have w37_98 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m37]; exact w36_98
    have w37_9c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m37]; exact w36_9c
    have w37_a0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m37]; exact w36_a0
    have w37_a4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m37]; exact w36_a4
    have w37_150 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m37]; exact w36_150
    have w37_154 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m37]; exact w36_154
    have w37_158 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m37]; exact w36_158
    have w37_15c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m37]; exact w36_15c
    have w37_408 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m37]; exact w36_408
    have w37_40c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m37]; exact w36_40c
    have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m37]; exact w36_420
    have w37_424 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m37]; exact w36_424
    clear w36_424 w36_420 w36_40c w36_408 w36_15c w36_158 w36_154 w36_150 w36_a4 w36_a0 w36_9c w36_98 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_44 w36_40 w36_3c w36_38 w36_34 w36_30 w36_2c g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_11 g36_10 g36_9 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
    exact .inl ⟨(fun ⟨h0', tb7', h1', vp14', vl14', h2', te14', h3', h4', h5', _⟩ => by rw [hr7] at h0'; cases h0'; rw [htb7] at h1'; cases h1'; rw [hr14] at h2'; cases h2'; rw [ht14] at h3'; cases h3'; rw [hr28] at h5'; cases h5'), sv_fail F E37 s37 t37 (fun x hx => (fR37 x hx).trans (fM x hx).symm) V37 hret g37_2 g37_18 hO g37_3 g37_4⟩
  rw [hr28] at R28
  obtain ⟨a0_28, a1_28⟩ := R28
  have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x0 := a0_28
  have g28_11 : reg n28 a1 = BitVec.ofNat 32 0x0 := by rw [a1_28]; rfl
  -- 0x498
  obtain ⟨n29, c29, u29⟩ := s28.block svX2c498 E28.self svX2c498_end
    ⟨trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem SV n29 0x49A (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock svX2c498 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
  have g29_9 : reg n29 (9 : Fin 32) = tbp := by
    rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
  have g29_11 : reg n29 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb29, runBlock_reg _ _ _ a1 s28.zero (by decide), g28_11]
  have g29_18 : reg n29 (18 : Fin 32) = out := by
    rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by
    rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = dg := by
    rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = rootp := by
    rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = ll := by
    rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = sgp := by
    rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = kp := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = sgl := by
    rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = tbl := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svX2c498, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_9, g28_10, g28_11, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m29]; exact w28_2c
  have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m29]; exact w28_30
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m29]; exact w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m29]; exact w28_38
  have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m29]; exact w28_3c
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m29]; exact w28_40
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m29]; exact w28_44
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m29]; exact w28_48
  have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m29]; exact w28_4c
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m29]; exact w28_50
  have w29_54 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m29]; exact w28_54
  have w29_58 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m29]; exact w28_58
  have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m29]; exact w28_5c
  have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m29]; exact w28_60
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m29]; exact w28_64
  have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m29]; exact w28_68
  have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m29]; exact w28_6c
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m29]; exact w28_70
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m29]; exact w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m29]; exact w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m29]; exact w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m29]; exact w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m29]; exact w28_84
  have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m29]; exact w28_88
  have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m29]; exact w28_8c
  have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m29]; exact w28_90
  have w29_94 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m29]; exact w28_94
  have w29_98 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m29]; exact w28_98
  have w29_9c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m29]; exact w28_9c
  have w29_a0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m29]; exact w28_a0
  have w29_a4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m29]; exact w28_a4
  have w29_150 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m29]; exact w28_150
  have w29_154 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m29]; exact w28_154
  have w29_158 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m29]; exact w28_158
  have w29_15c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m29]; exact w28_15c
  have w29_408 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m29]; exact w28_408
  have w29_40c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m29]; exact w28_40c
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m29]; exact w28_420
  have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m29]; exact w28_424
  clear w28_424 w28_420 w28_40c w28_408 w28_15c w28_158 w28_154 w28_150 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 w28_2c g28_2 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_4 g28_3 V28 E28 fR28 t28 fr28 K28 rk28 sp28 s28 c28
  -- 0x49A: sw
  obtain ⟨n30, d30, s30, fr30, K30, W30, rg30⟩ := sv_sw F E29 s29 sv_at_49a (off' := 0x49C) (c := 0x44)
    (by decide) (by rw [g29_2]; sv_addr) (by decide) (by decide)
  have t30 : Steps n0 n30 := t29.trans d30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keep K30 (by decide)
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rg30 sp, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg30 (3 : Fin 32), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg30 (4 : Fin 32), g29_4]
  have g30_9 : reg n30 (9 : Fin 32) = tbp := by rw [rg30 (9 : Fin 32), g29_9]
  have g30_10 : reg n30 a0 = BitVec.ofNat 32 0x0 := by rw [rg30 a0, g29_10]
  have g30_11 : reg n30 a1 = BitVec.ofNat 32 0x0 := by rw [rg30 a1, g29_11]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rg30 (18 : Fin 32), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rg30 (19 : Fin 32), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = dg := by rw [rg30 (20 : Fin 32), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = rootp := by rw [rg30 (21 : Fin 32), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = ll := by rw [rg30 (22 : Fin 32), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = sgp := by rw [rg30 (23 : Fin 32), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = kp := by rw [rg30 (24 : Fin 32), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = sgl := by rw [rg30 (25 : Fin 32), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg30 (26 : Fin 32), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = tbl := by rw [rg30 (27 : Fin 32), g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := keep_kk29.trans K30.toL
  clear keep_kk29
  have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K30.w32 (by decide) (by decide)).trans w29_2c
  have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K30.w32 (by decide) (by decide)).trans w29_30
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := (K30.w32 (by decide) (by decide)).trans w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := (K30.w32 (by decide) (by decide)).trans w29_38
  have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K30.w32 (by decide) (by decide)).trans w29_3c
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K30.w32 (by decide) (by decide)).trans w29_40
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K30.w32 (by decide) (by decide)).trans w29_48
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K30.w32 (by decide) (by decide)).trans w29_4c
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K30.w32 (by decide) (by decide)).trans w29_50
  have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K30.w32 (by decide) (by decide)).trans w29_54
  have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K30.w32 (by decide) (by decide)).trans w29_58
  have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K30.w32 (by decide) (by decide)).trans w29_5c
  have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K30.w32 (by decide) (by decide)).trans w29_60
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K30.w32 (by decide) (by decide)).trans w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K30.w32 (by decide) (by decide)).trans w29_68
  have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K30.w32 (by decide) (by decide)).trans w29_6c
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K30.w32 (by decide) (by decide)).trans w29_70
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K30.w32 (by decide) (by decide)).trans w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K30.w32 (by decide) (by decide)).trans w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K30.w32 (by decide) (by decide)).trans w29_7c
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K30.w32 (by decide) (by decide)).trans w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K30.w32 (by decide) (by decide)).trans w29_84
  have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K30.w32 (by decide) (by decide)).trans w29_88
  have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K30.w32 (by decide) (by decide)).trans w29_8c
  have w30_90 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K30.w32 (by decide) (by decide)).trans w29_90
  have w30_94 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K30.w32 (by decide) (by decide)).trans w29_94
  have w30_98 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K30.w32 (by decide) (by decide)).trans w29_98
  have w30_9c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K30.w32 (by decide) (by decide)).trans w29_9c
  have w30_a0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K30.w32 (by decide) (by decide)).trans w29_a0
  have w30_a4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K30.w32 (by decide) (by decide)).trans w29_a4
  have w30_150 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K30.w32 (by decide) (by decide)).trans w29_150
  have w30_154 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K30.w32 (by decide) (by decide)).trans w29_154
  have w30_158 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K30.w32 (by decide) (by decide)).trans w29_158
  have w30_15c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K30.w32 (by decide) (by decide)).trans w29_15c
  have w30_408 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := (K30.w32 (by decide) (by decide)).trans w29_408
  have w30_40c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := (K30.w32 (by decide) (by decide)).trans w29_40c
  have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := (K30.w32 (by decide) (by decide)).trans w29_420
  have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := (K30.w32 (by decide) (by decide)).trans w29_424
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x0 := by rw [W30, g29_11]
  clear w29_424 w29_420 w29_40c w29_408 w29_15c w29_158 w29_154 w29_150 w29_a4 w29_a0 w29_9c w29_98 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_44 w29_40 w29_3c w29_38 w29_34 w29_30 w29_2c g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_9 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29 g28_11 g28_10 a1_28 a0_28
  -- 0x49C: branch, not taken
  obtain ⟨n31, d31, u31⟩ := s30.notTaken E30.self 0x4A0 sv_at_49c
    (by decide) (by rw [g30_10, s30.zero]; decide)
  have s31 : St n31.mem SV n31 0x4A0 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, g30_4]
  have g31_9 : reg n31 (9 : Fin 32) = tbp := by rw [u31.regs, g30_9]
  have g31_10 : reg n31 a0 = BitVec.ofNat 32 0x0 := by rw [u31.regs, g30_10]
  have g31_11 : reg n31 a1 = BitVec.ofNat 32 0x0 := by rw [u31.regs, g30_11]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = dg := by rw [u31.regs, g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = rootp := by rw [u31.regs, g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = ll := by rw [u31.regs, g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = sgp := by rw [u31.regs, g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = kp := by rw [u31.regs, g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = sgl := by rw [u31.regs, g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u31.regs, g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = tbl := by rw [u31.regs, g30_27]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m31]; exact w30_2c
  have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m31]; exact w30_30
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m31]; exact w30_34
  have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m31]; exact w30_38
  have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m31]; exact w30_3c
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m31]; exact w30_40
  have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x0 := by rw [m31]; exact w30_44
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m31]; exact w30_48
  have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m31]; exact w30_4c
  have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m31]; exact w30_50
  have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m31]; exact w30_54
  have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m31]; exact w30_58
  have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m31]; exact w30_5c
  have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m31]; exact w30_60
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m31]; exact w30_64
  have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m31]; exact w30_68
  have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m31]; exact w30_6c
  have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m31]; exact w30_70
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m31]; exact w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m31]; exact w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m31]; exact w30_7c
  have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m31]; exact w30_80
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m31]; exact w30_84
  have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m31]; exact w30_88
  have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m31]; exact w30_8c
  have w31_90 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m31]; exact w30_90
  have w31_94 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m31]; exact w30_94
  have w31_98 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m31]; exact w30_98
  have w31_9c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m31]; exact w30_9c
  have w31_a0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m31]; exact w30_a0
  have w31_a4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m31]; exact w30_a4
  have w31_150 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m31]; exact w30_150
  have w31_154 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m31]; exact w30_154
  have w31_158 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m31]; exact w30_158
  have w31_15c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m31]; exact w30_15c
  have w31_408 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m31]; exact w30_408
  have w31_40c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m31]; exact w30_40c
  have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m31]; exact w30_420
  have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m31]; exact w30_424
  clear w30_44 w30_424 w30_420 w30_40c w30_408 w30_15c w30_158 w30_154 w30_150 w30_a4 w30_a0 w30_9c w30_98 w30_94 w30_90 w30_8c w30_88 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_48 w30_40 w30_3c w30_38 w30_34 w30_30 w30_2c g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_11 g30_10 g30_9 g30_4 g30_3 g30_2 V30 E30 fR30 t30 rg30 W30 K30 fr30 s30 d30
  -- 0x4A0: lw
  obtain ⟨n32, d32, u32⟩ := s31.lw E31.self sv_at_4a0 (off' := 0x4A2) (by decide)
    (by rw [g31_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s32 : St n32.mem SV n32 0x4A2 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
  have g32_9 : reg n32 (9 : Fin 32) = tbp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
  have g32_11 : reg n32 a1 = BitVec.ofNat 32 0x0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_11]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, upd_ne (by decide) (by decide), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = sgp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = kp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = sgl := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = tbl := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
  have g32_10 : reg n32 a0 = BitVec.ofNat 32 0x0 := by
    rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g31_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w31_44]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m32]; exact w31_2c
  have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m32]; exact w31_30
  have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m32]; exact w31_34
  have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m32]; exact w31_38
  have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m32]; exact w31_3c
  have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m32]; exact w31_40
  have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x0 := by rw [m32]; exact w31_44
  have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m32]; exact w31_48
  have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m32]; exact w31_4c
  have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m32]; exact w31_50
  have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m32]; exact w31_54
  have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m32]; exact w31_58
  have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m32]; exact w31_5c
  have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m32]; exact w31_60
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m32]; exact w31_64
  have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m32]; exact w31_68
  have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m32]; exact w31_6c
  have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m32]; exact w31_70
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m32]; exact w31_74
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m32]; exact w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m32]; exact w31_7c
  have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m32]; exact w31_80
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m32]; exact w31_84
  have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m32]; exact w31_88
  have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m32]; exact w31_8c
  have w32_90 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m32]; exact w31_90
  have w32_94 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m32]; exact w31_94
  have w32_98 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m32]; exact w31_98
  have w32_9c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m32]; exact w31_9c
  have w32_a0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m32]; exact w31_a0
  have w32_a4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m32]; exact w31_a4
  have w32_150 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m32]; exact w31_150
  have w32_154 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m32]; exact w31_154
  have w32_158 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m32]; exact w31_158
  have w32_15c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m32]; exact w31_15c
  have w32_408 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m32]; exact w31_408
  have w32_40c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m32]; exact w31_40c
  have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m32]; exact w31_420
  have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m32]; exact w31_424
  clear w31_424 w31_420 w31_40c w31_408 w31_15c w31_158 w31_154 w31_150 w31_a4 w31_a0 w31_9c w31_98 w31_94 w31_90 w31_8c w31_88 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_48 w31_44 w31_40 w31_3c w31_38 w31_34 w31_30 w31_2c g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_11 g31_10 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0x4A2
  obtain ⟨n33, c33, u33⟩ := s32.block svX2c4a2 E32.self svX2c4a2_end
    ⟨trivial, trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem SV n33 0x4A6 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock svX2c4a2 (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
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
  have g33_9 : reg n33 (9 : Fin 32) = tbp := by
    rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
  have g33_18 : reg n33 (18 : Fin 32) = out := by
    rw [rb33, runBlock_reg _ _ _ (18 : Fin 32) s32.zero (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by
    rw [rb33, runBlock_reg _ _ _ (19 : Fin 32) s32.zero (by decide), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = dg := by
    rw [rb33, runBlock_reg _ _ _ (20 : Fin 32) s32.zero (by decide), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = rootp := by
    rw [rb33, runBlock_reg _ _ _ (21 : Fin 32) s32.zero (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = ll := by
    rw [rb33, runBlock_reg _ _ _ (22 : Fin 32) s32.zero (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = sgp := by
    rw [rb33, runBlock_reg _ _ _ (23 : Fin 32) s32.zero (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = kp := by
    rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = sgl := by
    rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = tbl := by
    rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
  have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svX2c4a2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_9, g32_10, g32_11, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g33_11 : reg n33 a1 = BitVec.ofNat 32 0x16 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svX2c4a2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_9, g32_10, g32_11, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m33]; exact w32_2c
  have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m33]; exact w32_30
  have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m33]; exact w32_34
  have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m33]; exact w32_38
  have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m33]; exact w32_3c
  have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m33]; exact w32_40
  have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x0 := by rw [m33]; exact w32_44
  have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m33]; exact w32_48
  have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m33]; exact w32_4c
  have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m33]; exact w32_50
  have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m33]; exact w32_54
  have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m33]; exact w32_58
  have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m33]; exact w32_5c
  have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m33]; exact w32_60
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m33]; exact w32_64
  have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m33]; exact w32_68
  have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m33]; exact w32_6c
  have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m33]; exact w32_70
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m33]; exact w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m33]; exact w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m33]; exact w32_7c
  have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m33]; exact w32_80
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m33]; exact w32_84
  have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m33]; exact w32_88
  have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m33]; exact w32_8c
  have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m33]; exact w32_90
  have w33_94 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m33]; exact w32_94
  have w33_98 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m33]; exact w32_98
  have w33_9c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m33]; exact w32_9c
  have w33_a0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m33]; exact w32_a0
  have w33_a4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m33]; exact w32_a4
  have w33_150 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m33]; exact w32_150
  have w33_154 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m33]; exact w32_154
  have w33_158 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m33]; exact w32_158
  have w33_15c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m33]; exact w32_15c
  have w33_408 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m33]; exact w32_408
  have w33_40c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m33]; exact w32_40c
  have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m33]; exact w32_420
  have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m33]; exact w32_424
  clear w32_424 w32_420 w32_40c w32_408 w32_15c w32_158 w32_154 w32_150 w32_a4 w32_a0 w32_9c w32_98 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_48 w32_44 w32_40 w32_3c w32_38 w32_34 w32_30 w32_2c g32_10 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_9 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0x4A6: sw
  obtain ⟨n34, d34, s34, fr34, K34, W34, rg34⟩ := sv_sw F E33 s33 sv_at_4a6 (off' := 0x4A8) (c := 0x44)
    (by decide) (by rw [g33_2]; sv_addr) (by decide) (by decide)
  have t34 : Steps n0 n34 := t33.trans d34
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.keep K34 (by decide)
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [rg34 sp, g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg34 (3 : Fin 32), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg34 (4 : Fin 32), g33_4]
  have g34_9 : reg n34 (9 : Fin 32) = tbp := by rw [rg34 (9 : Fin 32), g33_9]
  have g34_10 : reg n34 a0 = BitVec.ofNat 32 0x0 := by rw [rg34 a0, g33_10]
  have g34_11 : reg n34 a1 = BitVec.ofNat 32 0x16 := by rw [rg34 a1, g33_11]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [rg34 (18 : Fin 32), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [rg34 (19 : Fin 32), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = dg := by rw [rg34 (20 : Fin 32), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = rootp := by rw [rg34 (21 : Fin 32), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = ll := by rw [rg34 (22 : Fin 32), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = sgp := by rw [rg34 (23 : Fin 32), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = kp := by rw [rg34 (24 : Fin 32), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = sgl := by rw [rg34 (25 : Fin 32), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg34 (26 : Fin 32), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = tbl := by rw [rg34 (27 : Fin 32), g33_27]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4)] := keep_kk33.trans K34.toL
  clear keep_kk33
  have w34_2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K34.w32 (by decide) (by decide)).trans w33_2c
  have w34_30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K34.w32 (by decide) (by decide)).trans w33_30
  have w34_34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := (K34.w32 (by decide) (by decide)).trans w33_34
  have w34_38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := (K34.w32 (by decide) (by decide)).trans w33_38
  have w34_3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K34.w32 (by decide) (by decide)).trans w33_3c
  have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K34.w32 (by decide) (by decide)).trans w33_40
  have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K34.w32 (by decide) (by decide)).trans w33_48
  have w34_4c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K34.w32 (by decide) (by decide)).trans w33_4c
  have w34_50 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K34.w32 (by decide) (by decide)).trans w33_50
  have w34_54 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K34.w32 (by decide) (by decide)).trans w33_54
  have w34_58 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K34.w32 (by decide) (by decide)).trans w33_58
  have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K34.w32 (by decide) (by decide)).trans w33_5c
  have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K34.w32 (by decide) (by decide)).trans w33_60
  have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K34.w32 (by decide) (by decide)).trans w33_64
  have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K34.w32 (by decide) (by decide)).trans w33_68
  have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K34.w32 (by decide) (by decide)).trans w33_6c
  have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K34.w32 (by decide) (by decide)).trans w33_70
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K34.w32 (by decide) (by decide)).trans w33_74
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K34.w32 (by decide) (by decide)).trans w33_78
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K34.w32 (by decide) (by decide)).trans w33_7c
  have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K34.w32 (by decide) (by decide)).trans w33_80
  have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K34.w32 (by decide) (by decide)).trans w33_84
  have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K34.w32 (by decide) (by decide)).trans w33_88
  have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K34.w32 (by decide) (by decide)).trans w33_8c
  have w34_90 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K34.w32 (by decide) (by decide)).trans w33_90
  have w34_94 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K34.w32 (by decide) (by decide)).trans w33_94
  have w34_98 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K34.w32 (by decide) (by decide)).trans w33_98
  have w34_9c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K34.w32 (by decide) (by decide)).trans w33_9c
  have w34_a0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K34.w32 (by decide) (by decide)).trans w33_a0
  have w34_a4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K34.w32 (by decide) (by decide)).trans w33_a4
  have w34_150 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K34.w32 (by decide) (by decide)).trans w33_150
  have w34_154 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K34.w32 (by decide) (by decide)).trans w33_154
  have w34_158 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K34.w32 (by decide) (by decide)).trans w33_158
  have w34_15c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K34.w32 (by decide) (by decide)).trans w33_15c
  have w34_408 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := (K34.w32 (by decide) (by decide)).trans w33_408
  have w34_40c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := (K34.w32 (by decide) (by decide)).trans w33_40c
  have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := (K34.w32 (by decide) (by decide)).trans w33_420
  have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := (K34.w32 (by decide) (by decide)).trans w33_424
  have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [W34, g33_11]
  clear w33_424 w33_420 w33_40c w33_408 w33_15c w33_158 w33_154 w33_150 w33_a4 w33_a0 w33_9c w33_98 w33_94 w33_90 w33_8c w33_88 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_48 w33_44 w33_40 w33_3c w33_38 w33_34 w33_30 w33_2c g33_11 g33_10 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
  -- 0x4A8: branch, not taken
  obtain ⟨n35, d35, u35⟩ := s34.notTaken E34.self 0x4AC sv_at_4a8
    (by decide) (by rw [g34_10, s34.zero]; decide)
  have s35 : St n35.mem SV n35 0x4AC (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans (.single d35)
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, g34_4]
  have g35_9 : reg n35 (9 : Fin 32) = tbp := by rw [u35.regs, g34_9]
  have g35_10 : reg n35 a0 = BitVec.ofNat 32 0x0 := by rw [u35.regs, g34_10]
  have g35_11 : reg n35 a1 = BitVec.ofNat 32 0x16 := by rw [u35.regs, g34_11]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = dg := by rw [u35.regs, g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = rootp := by rw [u35.regs, g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = ll := by rw [u35.regs, g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = sgp := by rw [u35.regs, g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = kp := by rw [u35.regs, g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = sgl := by rw [u35.regs, g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u35.regs, g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = tbl := by rw [u35.regs, g34_27]
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m35]; exact w34_2c
  have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m35]; exact w34_30
  have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m35]; exact w34_34
  have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m35]; exact w34_38
  have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m35]; exact w34_3c
  have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m35]; exact w34_40
  have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m35]; exact w34_44
  have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m35]; exact w34_48
  have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m35]; exact w34_4c
  have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m35]; exact w34_50
  have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m35]; exact w34_54
  have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m35]; exact w34_58
  have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m35]; exact w34_5c
  have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m35]; exact w34_60
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m35]; exact w34_64
  have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m35]; exact w34_68
  have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m35]; exact w34_6c
  have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m35]; exact w34_70
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m35]; exact w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m35]; exact w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m35]; exact w34_7c
  have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m35]; exact w34_80
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m35]; exact w34_84
  have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m35]; exact w34_88
  have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m35]; exact w34_8c
  have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m35]; exact w34_90
  have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m35]; exact w34_94
  have w35_98 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m35]; exact w34_98
  have w35_9c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m35]; exact w34_9c
  have w35_a0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m35]; exact w34_a0
  have w35_a4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m35]; exact w34_a4
  have w35_150 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m35]; exact w34_150
  have w35_154 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m35]; exact w34_154
  have w35_158 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m35]; exact w34_158
  have w35_15c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m35]; exact w34_15c
  have w35_408 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m35]; exact w34_408
  have w35_40c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m35]; exact w34_40c
  have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m35]; exact w34_420
  have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m35]; exact w34_424
  clear w34_44 w34_424 w34_420 w34_40c w34_408 w34_15c w34_158 w34_154 w34_150 w34_a4 w34_a0 w34_9c w34_98 w34_94 w34_90 w34_8c w34_88 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_40 w34_3c w34_38 w34_34 w34_30 w34_2c g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_11 g34_10 g34_9 g34_4 g34_3 g34_2 V34 E34 fR34 t34 rg34 W34 K34 fr34 s34 d34
  -- 0x4AC: branch, not taken
  obtain ⟨n36, d36, u36⟩ := s35.notTaken E35.self 0x4B0 sv_at_4ac
    (by decide) (by rw [g35_26, s35.zero]; decide)
  have s36 : St n36.mem SV n36 0x4B0 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, g35_4]
  have g36_9 : reg n36 (9 : Fin 32) = tbp := by rw [u36.regs, g35_9]
  have g36_10 : reg n36 a0 = BitVec.ofNat 32 0x0 := by rw [u36.regs, g35_10]
  have g36_11 : reg n36 a1 = BitVec.ofNat 32 0x16 := by rw [u36.regs, g35_11]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = dg := by rw [u36.regs, g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = rootp := by rw [u36.regs, g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = ll := by rw [u36.regs, g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = sgp := by rw [u36.regs, g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = kp := by rw [u36.regs, g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = sgl := by rw [u36.regs, g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u36.regs, g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = tbl := by rw [u36.regs, g35_27]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m36]; exact w35_2c
  have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m36]; exact w35_30
  have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m36]; exact w35_34
  have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m36]; exact w35_38
  have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m36]; exact w35_3c
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m36]; exact w35_40
  have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m36]; exact w35_44
  have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m36]; exact w35_48
  have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m36]; exact w35_4c
  have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m36]; exact w35_50
  have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m36]; exact w35_54
  have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m36]; exact w35_58
  have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m36]; exact w35_5c
  have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m36]; exact w35_60
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m36]; exact w35_64
  have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m36]; exact w35_68
  have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m36]; exact w35_6c
  have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m36]; exact w35_70
  have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m36]; exact w35_74
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m36]; exact w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m36]; exact w35_7c
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m36]; exact w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m36]; exact w35_84
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m36]; exact w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m36]; exact w35_8c
  have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m36]; exact w35_90
  have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m36]; exact w35_94
  have w36_98 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m36]; exact w35_98
  have w36_9c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m36]; exact w35_9c
  have w36_a0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m36]; exact w35_a0
  have w36_a4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m36]; exact w35_a4
  have w36_150 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m36]; exact w35_150
  have w36_154 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m36]; exact w35_154
  have w36_158 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m36]; exact w35_158
  have w36_15c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m36]; exact w35_15c
  have w36_408 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m36]; exact w35_408
  have w36_40c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m36]; exact w35_40c
  have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m36]; exact w35_420
  have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m36]; exact w35_424
  clear w35_424 w35_420 w35_40c w35_408 w35_15c w35_158 w35_154 w35_150 w35_a4 w35_a0 w35_9c w35_98 w35_94 w35_90 w35_8c w35_88 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_44 w35_40 w35_3c w35_38 w35_34 w35_30 w35_2c g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_11 g35_10 g35_9 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
  -- 0x4B0
  obtain ⟨n37, c37, u37⟩ := s36.block svX2c4b0 E36.self svX2c4b0_end
    ⟨trivial, trivial⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have s37 : St n37.mem SV n37 0x4B4 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have rb37 : ∀ q, reg n37 q = (runBlock svX2c4b0 (n36.mem, reg n36)).2 q := fun q => by rw [u37.regs]
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans c37
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by
    rw [rb37, runBlock_reg _ _ _ sp s36.zero (by decide), g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb37, runBlock_reg _ _ _ (3 : Fin 32) s36.zero (by decide), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb37, runBlock_reg _ _ _ (4 : Fin 32) s36.zero (by decide), g36_4]
  have g37_9 : reg n37 (9 : Fin 32) = tbp := by
    rw [rb37, runBlock_reg _ _ _ (9 : Fin 32) s36.zero (by decide), g36_9]
  have g37_11 : reg n37 a1 = BitVec.ofNat 32 0x16 := by
    rw [rb37, runBlock_reg _ _ _ a1 s36.zero (by decide), g36_11]
  have g37_18 : reg n37 (18 : Fin 32) = out := by
    rw [rb37, runBlock_reg _ _ _ (18 : Fin 32) s36.zero (by decide), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by
    rw [rb37, runBlock_reg _ _ _ (19 : Fin 32) s36.zero (by decide), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = dg := by
    rw [rb37, runBlock_reg _ _ _ (20 : Fin 32) s36.zero (by decide), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = rootp := by
    rw [rb37, runBlock_reg _ _ _ (21 : Fin 32) s36.zero (by decide), g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = ll := by
    rw [rb37, runBlock_reg _ _ _ (22 : Fin 32) s36.zero (by decide), g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = sgp := by
    rw [rb37, runBlock_reg _ _ _ (23 : Fin 32) s36.zero (by decide), g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = kp := by
    rw [rb37, runBlock_reg _ _ _ (24 : Fin 32) s36.zero (by decide), g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = sgl := by
    rw [rb37, runBlock_reg _ _ _ (25 : Fin 32) s36.zero (by decide), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb37, runBlock_reg _ _ _ (26 : Fin 32) s36.zero (by decide), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = tbl := by
    rw [rb37, runBlock_reg _ _ _ (27 : Fin 32) s36.zero (by decide), g36_27]
  have g37_10 : reg n37 a0 = BitVec.ofNat 32 0x20 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, svX2c4b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_9, g36_10, g36_11, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, s36.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4)] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have w37_2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m37]; exact w36_2c
  have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m37]; exact w36_30
  have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m37]; exact w36_34
  have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m37]; exact w36_38
  have w37_3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m37]; exact w36_3c
  have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m37]; exact w36_40
  have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m37]; exact w36_44
  have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m37]; exact w36_48
  have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m37]; exact w36_4c
  have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m37]; exact w36_50
  have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m37]; exact w36_54
  have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m37]; exact w36_58
  have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m37]; exact w36_5c
  have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m37]; exact w36_60
  have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m37]; exact w36_64
  have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m37]; exact w36_68
  have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m37]; exact w36_6c
  have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m37]; exact w36_70
  have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m37]; exact w36_74
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m37]; exact w36_78
  have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m37]; exact w36_7c
  have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m37]; exact w36_80
  have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m37]; exact w36_84
  have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m37]; exact w36_88
  have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m37]; exact w36_8c
  have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m37]; exact w36_90
  have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m37]; exact w36_94
  have w37_98 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m37]; exact w36_98
  have w37_9c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m37]; exact w36_9c
  have w37_a0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m37]; exact w36_a0
  have w37_a4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m37]; exact w36_a4
  have w37_150 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m37]; exact w36_150
  have w37_154 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m37]; exact w36_154
  have w37_158 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m37]; exact w36_158
  have w37_15c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m37]; exact w36_15c
  have w37_408 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m37]; exact w36_408
  have w37_40c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m37]; exact w36_40c
  have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m37]; exact w36_420
  have w37_424 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m37]; exact w36_424
  clear w36_424 w36_420 w36_40c w36_408 w36_15c w36_158 w36_154 w36_150 w36_a4 w36_a0 w36_9c w36_98 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_44 w36_40 w36_3c w36_38 w36_34 w36_30 w36_2c g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_11 g36_10 g36_9 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
  -- 0x4B4: sw
  obtain ⟨n38, d38, s38, fr38, K38, W38, rg38⟩ := sv_sw F E37 s37 sv_at_4b4 (off' := 0x4B6) (c := 0x50)
    (by decide) (by rw [g37_2]; sv_addr) (by decide) (by decide)
  have t38 : Steps n0 n38 := t37.trans d38
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.keep K38 (by decide)
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [rg38 sp, g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg38 (3 : Fin 32), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg38 (4 : Fin 32), g37_4]
  have g38_9 : reg n38 (9 : Fin 32) = tbp := by rw [rg38 (9 : Fin 32), g37_9]
  have g38_10 : reg n38 a0 = BitVec.ofNat 32 0x20 := by rw [rg38 a0, g37_10]
  have g38_11 : reg n38 a1 = BitVec.ofNat 32 0x16 := by rw [rg38 a1, g37_11]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [rg38 (18 : Fin 32), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [rg38 (19 : Fin 32), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = dg := by rw [rg38 (20 : Fin 32), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = rootp := by rw [rg38 (21 : Fin 32), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = ll := by rw [rg38 (22 : Fin 32), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = sgp := by rw [rg38 (23 : Fin 32), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = kp := by rw [rg38 (24 : Fin 32), g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = sgl := by rw [rg38 (25 : Fin 32), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg38 (26 : Fin 32), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = tbl := by rw [rg38 (27 : Fin 32), g37_27]
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4), (0x50, 0x4)] := keep_kk37.trans K38.toL
  clear keep_kk37
  have w38_2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K38.w32 (by decide) (by decide)).trans w37_2c
  have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K38.w32 (by decide) (by decide)).trans w37_30
  have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := (K38.w32 (by decide) (by decide)).trans w37_34
  have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := (K38.w32 (by decide) (by decide)).trans w37_38
  have w38_3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K38.w32 (by decide) (by decide)).trans w37_3c
  have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K38.w32 (by decide) (by decide)).trans w37_40
  have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K38.w32 (by decide) (by decide)).trans w37_44
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K38.w32 (by decide) (by decide)).trans w37_48
  have w38_4c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K38.w32 (by decide) (by decide)).trans w37_4c
  have w38_54 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K38.w32 (by decide) (by decide)).trans w37_54
  have w38_58 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K38.w32 (by decide) (by decide)).trans w37_58
  have w38_5c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K38.w32 (by decide) (by decide)).trans w37_5c
  have w38_60 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K38.w32 (by decide) (by decide)).trans w37_60
  have w38_64 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K38.w32 (by decide) (by decide)).trans w37_64
  have w38_68 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K38.w32 (by decide) (by decide)).trans w37_68
  have w38_6c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K38.w32 (by decide) (by decide)).trans w37_6c
  have w38_70 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K38.w32 (by decide) (by decide)).trans w37_70
  have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K38.w32 (by decide) (by decide)).trans w37_74
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K38.w32 (by decide) (by decide)).trans w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K38.w32 (by decide) (by decide)).trans w37_7c
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K38.w32 (by decide) (by decide)).trans w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K38.w32 (by decide) (by decide)).trans w37_84
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K38.w32 (by decide) (by decide)).trans w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K38.w32 (by decide) (by decide)).trans w37_8c
  have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K38.w32 (by decide) (by decide)).trans w37_90
  have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K38.w32 (by decide) (by decide)).trans w37_94
  have w38_98 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K38.w32 (by decide) (by decide)).trans w37_98
  have w38_9c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K38.w32 (by decide) (by decide)).trans w37_9c
  have w38_a0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K38.w32 (by decide) (by decide)).trans w37_a0
  have w38_a4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K38.w32 (by decide) (by decide)).trans w37_a4
  have w38_150 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K38.w32 (by decide) (by decide)).trans w37_150
  have w38_154 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K38.w32 (by decide) (by decide)).trans w37_154
  have w38_158 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K38.w32 (by decide) (by decide)).trans w37_158
  have w38_15c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K38.w32 (by decide) (by decide)).trans w37_15c
  have w38_408 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := (K38.w32 (by decide) (by decide)).trans w37_408
  have w38_40c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := (K38.w32 (by decide) (by decide)).trans w37_40c
  have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := (K38.w32 (by decide) (by decide)).trans w37_420
  have w38_424 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := (K38.w32 (by decide) (by decide)).trans w37_424
  have w38_50 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x20 := by rw [W38, g37_10]
  clear w37_424 w37_420 w37_40c w37_408 w37_15c w37_158 w37_154 w37_150 w37_a4 w37_a0 w37_9c w37_98 w37_94 w37_90 w37_8c w37_88 w37_84 w37_80 w37_7c w37_78 w37_74 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 w37_50 w37_4c w37_48 w37_44 w37_40 w37_3c w37_38 w37_34 w37_30 w37_2c g37_10 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_11 g37_9 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 rb37 s37 m37 u37 c37
  -- 0x4B6
  obtain ⟨n39, c39, u39⟩ := s38.block svX2c4b6 E38.self svX2c4b6_end
    ⟨trivial, trivial, trivial⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have s39 : St n39.mem SV n39 0x4BE (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have rb39 : ∀ q, reg n39 q = (runBlock svX2c4b6 (n38.mem, reg n38)).2 q := fun q => by rw [u39.regs]
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
  have g39_9 : reg n39 (9 : Fin 32) = tbp := by
    rw [rb39, runBlock_reg _ _ _ (9 : Fin 32) s38.zero (by decide), g38_9]
  have g39_10 : reg n39 a0 = BitVec.ofNat 32 0x20 := by
    rw [rb39, runBlock_reg _ _ _ a0 s38.zero (by decide), g38_10]
  have g39_11 : reg n39 a1 = BitVec.ofNat 32 0x16 := by
    rw [rb39, runBlock_reg _ _ _ a1 s38.zero (by decide), g38_11]
  have g39_18 : reg n39 (18 : Fin 32) = out := by
    rw [rb39, runBlock_reg _ _ _ (18 : Fin 32) s38.zero (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by
    rw [rb39, runBlock_reg _ _ _ (19 : Fin 32) s38.zero (by decide), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = dg := by
    rw [rb39, runBlock_reg _ _ _ (20 : Fin 32) s38.zero (by decide), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = rootp := by
    rw [rb39, runBlock_reg _ _ _ (21 : Fin 32) s38.zero (by decide), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = ll := by
    rw [rb39, runBlock_reg _ _ _ (22 : Fin 32) s38.zero (by decide), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = sgp := by
    rw [rb39, runBlock_reg _ _ _ (23 : Fin 32) s38.zero (by decide), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = kp := by
    rw [rb39, runBlock_reg _ _ _ (24 : Fin 32) s38.zero (by decide), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = sgl := by
    rw [rb39, runBlock_reg _ _ _ (25 : Fin 32) s38.zero (by decide), g38_25]
  have g39_27 : reg n39 (27 : Fin 32) = tbl := by
    rw [rb39, runBlock_reg _ _ _ (27 : Fin 32) s38.zero (by decide), g38_27]
  have g39_26 : reg n39 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x11) := by
    rw [rb39]; simp +decide only [runBlock, BInstr.run, svX2c4b6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g38_2, g38_3, g38_4, g38_9, g38_10, g38_11, g38_18, g38_19, g38_20, g38_21, g38_22, g38_23, g38_24, g38_25, g38_26, g38_27, s38.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4), (0x50, 0x4)] := by rw [m39]; exact keep_kk38
  clear keep_kk38
  have w39_2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m39]; exact w38_2c
  have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m39]; exact w38_30
  have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl14 := by rw [m39]; exact w38_34
  have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp14 := by rw [m39]; exact w38_38
  have w39_3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m39]; exact w38_3c
  have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m39]; exact w38_40
  have w39_44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m39]; exact w38_44
  have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m39]; exact w38_48
  have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m39]; exact w38_4c
  have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x20 := by rw [m39]; exact w38_50
  have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m39]; exact w38_54
  have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m39]; exact w38_58
  have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m39]; exact w38_5c
  have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m39]; exact w38_60
  have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m39]; exact w38_64
  have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m39]; exact w38_68
  have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m39]; exact w38_6c
  have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m39]; exact w38_70
  have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m39]; exact w38_74
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m39]; exact w38_78
  have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m39]; exact w38_7c
  have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m39]; exact w38_80
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m39]; exact w38_84
  have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m39]; exact w38_88
  have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m39]; exact w38_8c
  have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m39]; exact w38_90
  have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m39]; exact w38_94
  have w39_98 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m39]; exact w38_98
  have w39_9c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m39]; exact w38_9c
  have w39_a0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m39]; exact w38_a0
  have w39_a4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m39]; exact w38_a4
  have w39_150 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m39]; exact w38_150
  have w39_154 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m39]; exact w38_154
  have w39_158 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m39]; exact w38_158
  have w39_15c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m39]; exact w38_15c
  have w39_408 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((rp2) + BitVec.ofNat 32 (tb7.header + tb7.len)) + BitVec.ofNat 32 (te14.header + te14.len) := by rw [m39]; exact w38_408
  have w39_40c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = ((rem2) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) := by rw [m39]; exact w38_40c
  have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp14 := by rw [m39]; exact w38_420
  have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl14 := by rw [m39]; exact w38_424
  clear w38_50 w38_424 w38_420 w38_40c w38_408 w38_15c w38_158 w38_154 w38_150 w38_a4 w38_a0 w38_9c w38_98 w38_94 w38_90 w38_8c w38_88 w38_84 w38_80 w38_7c w38_78 w38_74 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 w38_4c w38_48 w38_44 w38_40 w38_3c w38_38 w38_34 w38_30 w38_2c g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_11 g38_10 g38_9 g38_4 g38_3 g38_2 V38 E38 fR38 t38 rg38 W38 K38 fr38 s38 d38
  exact .inr ⟨hr7, tb7, htb7, vp14, vl14, hr14, te14, ht14, hz_18, hr28, n39, t39, s39, E39, V39, fR39, g39_2, g39_3, g39_4, g39_9, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, w39_2c, w39_30, w39_34, w39_38, w39_3c, w39_40, w39_48, w39_4c, w39_50, w39_54, w39_58, w39_5c, w39_60, w39_64, w39_68, w39_6c, w39_70, w39_74, w39_78, w39_7c, w39_80, w39_84, w39_88, w39_8c, w39_90, w39_94, w39_98, w39_9c, w39_a0, w39_a4, w39_150, w39_154, w39_158, w39_15c, keep_kk39.mono (by decide)⟩

end C3.RV32.Sv
