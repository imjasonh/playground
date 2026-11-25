import C3BootProofs.Proofs.SvData

/-!
# `sigstore::verify`: an extension's OID

One pass of the extensions loop, from its head at 0x3B8 to the criticality test at 0x42C: the next extension is a `SEQUENCE` that starts with an OID.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svX1938 : List BInstr :=
  [.aluImm .add a0 x0 0x6]
theorem svX1938_end : blockEnd sigstoreVerifyCode 0x938 svX1938 = some 0x93A := by
  simp only [svX1938]
  rw [blockEnd, sv_at_938]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX13d0 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x150]
theorem svX13d0_end : blockEnd sigstoreVerifyCode 0x3D0 svX13d0 = some 0x3D6 := by
  simp only [svX13d0]
  rw [blockEnd, sv_at_3d0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_3d4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX13ec : List BInstr :=
  [.aluImm .add a2 x0 0xB, .aluImm .add a0 sp 0x405, .aluImm .add a1 sp 0x425]
theorem svX13ec_end : blockEnd sigstoreVerifyCode 0x3EC svX13ec = some 0x3F6 := by
  simp only [svX13ec]
  rw [blockEnd, sv_at_3ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_3ee]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_3f2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX1408 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x400]
theorem svX1408_end : blockEnd sigstoreVerifyCode 0x408 svX1408 = some 0x410 := by
  simp only [svX1408]
  rw [blockEnd, sv_at_408]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_40c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_x1 {B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x3B8 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = BitVec.ofNat 32 0x15)
    (g0_9 : reg n0 (9 : Fin 32) = tbp)
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
    (w0_158 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur)
    (w0_15c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem)
    (xl_in : SvIn B (cur) (rem).toNat)
    (ea_in : SvIn B p0 (L.toNat - rem.toNat))
    (hrem : rem ≠ 0) :
    (¬ ((rem.toNat ≤ L.toNat) ∧ ∃ tl10, derElement 0x30 (memBytes M0 (cur) (rem).toNat) = .ok tl10 ∧ ∃ op21 ol21, derContent ((cur) + BitVec.ofNat 32 tl10.header) (derOid (memBytes M0 ((cur) + BitVec.ofNat 32 tl10.header) (BitVec.ofNat 32 tl10.len).toNat)) = .ok (op21, ol21) ∧ ∃ to21, derOid (memBytes M0 ((cur) + BitVec.ofNat 32 tl10.header) (BitVec.ofNat 32 tl10.len).toNat) = .ok to21 ∧ True) ∧ SvErrRet B out v n0) ∨
    ((rem.toNat ≤ L.toNat) ∧
    ∃ tl10, derElement 0x30 (memBytes M0 (cur) (rem).toNat) = .ok tl10 ∧
    ∃ op21 ol21, derContent ((cur) + BitVec.ofNat 32 tl10.header) (derOid (memBytes M0 ((cur) + BitVec.ofNat 32 tl10.header) (BitVec.ofNat 32 tl10.len).toNat)) = .ok (op21, ol21) ∧
    ∃ to21, derOid (memBytes M0 ((cur) + BitVec.ofNat 32 tl10.header) (BitVec.ofNat 32 tl10.len).toNat) = .ok to21 ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x42C (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x15 ∧
        reg n' (9 : Fin 32) = tbp ∧
        reg n' a0 = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) ∧
        reg n' a1 = ol21 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (23 : Fin 32) = sgp ∧
        reg n' (24 : Fin 32) = kp ∧
        reg n' (25 : Fin 32) = sgl ∧
        reg n' (27 : Fin 32) = tbl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol21 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op21 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((cur) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (to21.header + to21.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) ∧
        SvKeepL B n0.mem n'.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4), (0x48, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x3B8: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_3b8 (off' := 0x3BA) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0x3BA (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = tbp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, upd_ne (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = dg := by rw [u1.regs, upd_ne (by decide) (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = rootp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = ll := by rw [u1.regs, upd_ne (by decide) (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = sgp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = kp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = sgl := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_27 : reg n1 (27 : Fin 32) = tbl := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_10 : reg n1 a0 = rem := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w0_50]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m1]; exact w0_2c
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m1]; exact w0_30
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
  have w1_15c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m1]; exact w0_15c
  -- 0x3BA: branch, not taken
  obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.self 0x3BE sv_at_3ba
    (by decide) (by rw [g1_10, s1.zero]; exact br_beq_f hrem)
  have s2 : St n2.mem SV n2 0x3BE (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u2.regs, g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = tbp := by rw [u2.regs, g1_9]
  have g2_10 : reg n2 a0 = rem := by rw [u2.regs, g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [u2.regs, g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [u2.regs, g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [u2.regs, g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = sgp := by rw [u2.regs, g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = kp := by rw [u2.regs, g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = sgl := by rw [u2.regs, g1_25]
  have g2_27 : reg n2 (27 : Fin 32) = tbl := by rw [u2.regs, g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m2]; exact w1_2c
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m2]; exact w1_30
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
  have w2_15c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m2]; exact w1_15c
  clear w1_15c w1_158 w1_154 w1_150 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_30 w1_2c g1_10 g1_27 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x3BE: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_3be (off' := 0x3C2) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x154 = B + 0x21A0 + BitVec.ofNat 32 0x154 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x3C2 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = tbp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_10 : reg n3 a0 = rem := by rw [u3.regs, upd_ne (by decide) (by decide), g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = sgp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = kp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = sgl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_27 : reg n3 (27 : Fin 32) = tbl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_11 : reg n3 a1 = L := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x154 = B + 0x21A0 + BitVec.ofNat 32 0x154 by sv_addr, w2_154]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m3]; exact w2_2c
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m3]; exact w2_30
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
  have w3_15c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m3]; exact w2_15c
  clear w2_15c w2_158 w2_154 w2_150 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_74 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_30 w2_2c g2_27 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x3C2: lw
  obtain ⟨n4, d4, u4⟩ := s3.lw E3.self sv_at_3c2 (off' := 0x3C4) (by decide)
    (by rw [g3_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s4 : St n4.mem SV n4 0x3C4 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = tbp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_9]
  have g4_11 : reg n4 a1 = L := by rw [u4.regs, upd_ne (by decide) (by decide), g3_11]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = sgp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = kp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = sgl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
  have g4_27 : reg n4 (27 : Fin 32) = tbl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
  have g4_10 : reg n4 a0 = rem := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w3_50]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m4]; exact w3_2c
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m4]; exact w3_30
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
  have w4_15c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m4]; exact w3_15c
  clear w3_15c w3_158 w3_154 w3_150 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_30 w3_2c g3_11 g3_27 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x3C4: sw
  obtain ⟨n5, d5, s5, fr5, K5, W5, rg5⟩ := sv_sw F E4 s4 sv_at_3c4 (off' := 0x3C6) (c := 0x40)
    (by decide) (by rw [g4_2]; sv_addr) (by decide) (by decide)
  have t5 : Steps n0 n5 := t4.trans d5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keep K5 (by decide)
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rg5 sp, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg5 (3 : Fin 32), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg5 (4 : Fin 32), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg5 (8 : Fin 32), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = tbp := by rw [rg5 (9 : Fin 32), g4_9]
  have g5_10 : reg n5 a0 = rem := by rw [rg5 a0, g4_10]
  have g5_11 : reg n5 a1 = L := by rw [rg5 a1, g4_11]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [rg5 (18 : Fin 32), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [rg5 (19 : Fin 32), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = dg := by rw [rg5 (20 : Fin 32), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = rootp := by rw [rg5 (21 : Fin 32), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = ll := by rw [rg5 (22 : Fin 32), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = sgp := by rw [rg5 (23 : Fin 32), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = kp := by rw [rg5 (24 : Fin 32), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = sgl := by rw [rg5 (25 : Fin 32), g4_25]
  have g5_27 : reg n5 (27 : Fin 32) = tbl := by rw [rg5 (27 : Fin 32), g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x40, 0x4)] := keep_kk4.trans K5.toL
  clear keep_kk4
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K5.w32 (by decide) (by decide)).trans w4_2c
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K5.w32 (by decide) (by decide)).trans w4_30
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K5.w32 (by decide) (by decide)).trans w4_50
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K5.w32 (by decide) (by decide)).trans w4_54
  have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K5.w32 (by decide) (by decide)).trans w4_58
  have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K5.w32 (by decide) (by decide)).trans w4_5c
  have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K5.w32 (by decide) (by decide)).trans w4_60
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K5.w32 (by decide) (by decide)).trans w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K5.w32 (by decide) (by decide)).trans w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K5.w32 (by decide) (by decide)).trans w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K5.w32 (by decide) (by decide)).trans w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K5.w32 (by decide) (by decide)).trans w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K5.w32 (by decide) (by decide)).trans w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K5.w32 (by decide) (by decide)).trans w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K5.w32 (by decide) (by decide)).trans w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K5.w32 (by decide) (by decide)).trans w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K5.w32 (by decide) (by decide)).trans w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K5.w32 (by decide) (by decide)).trans w4_8c
  have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K5.w32 (by decide) (by decide)).trans w4_90
  have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K5.w32 (by decide) (by decide)).trans w4_94
  have w5_98 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K5.w32 (by decide) (by decide)).trans w4_98
  have w5_9c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K5.w32 (by decide) (by decide)).trans w4_9c
  have w5_a0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K5.w32 (by decide) (by decide)).trans w4_a0
  have w5_a4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K5.w32 (by decide) (by decide)).trans w4_a4
  have w5_150 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K5.w32 (by decide) (by decide)).trans w4_150
  have w5_154 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K5.w32 (by decide) (by decide)).trans w4_154
  have w5_158 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K5.w32 (by decide) (by decide)).trans w4_158
  have w5_15c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := (K5.w32 (by decide) (by decide)).trans w4_15c
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [W5, g4_11]
  clear w4_15c w4_158 w4_154 w4_150 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_30 w4_2c g4_10 g4_27 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_11 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  by_cases hz_5 : rem.toNat ≤ L.toNat
  rotate_left
  · -- 0x3C6: branch, taken
    obtain ⟨n6, d6, u6⟩ := s5.taken E5.self 0x938 sv_at_3c6
      (by decide) (by rw [g5_11, g5_10]; exact br_bltu_t (by omega))
    have s6 : St n6.mem SV n6 0x938 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
    have t6 : Steps n0 n6 := t5.trans (.single d6)
    have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
    have E6 : SvCode n6.mem := E5.fr F fr6
    have V6 : SvSaves B n6.mem v := V5.same m6
    have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
    have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
    have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
    have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u6.regs, g5_8]
    have g6_9 : reg n6 (9 : Fin 32) = tbp := by rw [u6.regs, g5_9]
    have g6_10 : reg n6 a0 = rem := by rw [u6.regs, g5_10]
    have g6_11 : reg n6 a1 = L := by rw [u6.regs, g5_11]
    have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
    have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [u6.regs, g5_20]
    have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [u6.regs, g5_21]
    have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [u6.regs, g5_22]
    have g6_23 : reg n6 (23 : Fin 32) = sgp := by rw [u6.regs, g5_23]
    have g6_24 : reg n6 (24 : Fin 32) = kp := by rw [u6.regs, g5_24]
    have g6_25 : reg n6 (25 : Fin 32) = sgl := by rw [u6.regs, g5_25]
    have g6_27 : reg n6 (27 : Fin 32) = tbl := by rw [u6.regs, g5_27]
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x40, 0x4)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m6]; exact w5_2c
    have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m6]; exact w5_30
    have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m6]; exact w5_40
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
    have w6_15c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m6]; exact w5_15c
    clear w5_40 w5_15c w5_158 w5_154 w5_150 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_30 w5_2c g5_27 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_11 g5_10 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 rg5 W5 K5 fr5 s5 d5
    -- 0x938
    obtain ⟨n7, c7, u7⟩ := s6.block svX1938 E6.self svX1938_end
      ⟨trivial, trivial⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have s7 : St n7.mem SV n7 0x93A (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have rb7 : ∀ q, reg n7 q = (runBlock svX1938 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans c7
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by
      rw [rb7, runBlock_reg _ _ _ sp s6.zero (by decide), g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb7, runBlock_reg _ _ _ (3 : Fin 32) s6.zero (by decide), g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb7, runBlock_reg _ _ _ (4 : Fin 32) s6.zero (by decide), g6_4]
    have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb7, runBlock_reg _ _ _ (8 : Fin 32) s6.zero (by decide), g6_8]
    have g7_9 : reg n7 (9 : Fin 32) = tbp := by
      rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
    have g7_11 : reg n7 a1 = L := by
      rw [rb7, runBlock_reg _ _ _ a1 s6.zero (by decide), g6_11]
    have g7_18 : reg n7 (18 : Fin 32) = out := by
      rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by
      rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = dg := by
      rw [rb7, runBlock_reg _ _ _ (20 : Fin 32) s6.zero (by decide), g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = rootp := by
      rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = ll := by
      rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = sgp := by
      rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = kp := by
      rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = sgl := by
      rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
    have g7_27 : reg n7 (27 : Fin 32) = tbl := by
      rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
    have g7_10 : reg n7 a0 = BitVec.ofNat 32 0x6 := by
      rw [rb7]; simp +decide only [runBlock, BInstr.run, svX1938, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_11, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_27, s6.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x40, 0x4)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m7]; exact w6_2c
    have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m7]; exact w6_30
    have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m7]; exact w6_40
    have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m7]; exact w6_50
    have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m7]; exact w6_54
    have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m7]; exact w6_58
    have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m7]; exact w6_5c
    have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m7]; exact w6_60
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
    have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m7]; exact w6_68
    have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m7]; exact w6_6c
    have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m7]; exact w6_70
    have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m7]; exact w6_74
    have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m7]; exact w6_78
    have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m7]; exact w6_7c
    have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m7]; exact w6_80
    have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m7]; exact w6_84
    have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m7]; exact w6_88
    have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m7]; exact w6_8c
    have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m7]; exact w6_90
    have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m7]; exact w6_94
    have w7_98 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m7]; exact w6_98
    have w7_9c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m7]; exact w6_9c
    have w7_a0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m7]; exact w6_a0
    have w7_a4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m7]; exact w6_a4
    have w7_150 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m7]; exact w6_150
    have w7_154 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m7]; exact w6_154
    have w7_158 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m7]; exact w6_158
    have w7_15c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m7]; exact w6_15c
    clear w6_15c w6_158 w6_154 w6_150 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_40 w6_30 w6_2c g6_27 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
    -- 0x93A: j
    obtain ⟨n8, d8, u8⟩ := s7.jump E7.self sv_at_93a (off' := 0x942) (by decide)
      (by rw [s7.pc]; decide)
    have s8 : St n8.mem SV n8 0x942 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
    have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u8.regs, g7_8]
    have g8_9 : reg n8 (9 : Fin 32) = tbp := by rw [u8.regs, g7_9]
    have g8_10 : reg n8 a0 = BitVec.ofNat 32 0x6 := by rw [u8.regs, g7_10]
    have g8_11 : reg n8 a1 = L := by rw [u8.regs, g7_11]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [u8.regs, g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [u8.regs, g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [u8.regs, g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = sgp := by rw [u8.regs, g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = kp := by rw [u8.regs, g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = sgl := by rw [u8.regs, g7_25]
    have g8_27 : reg n8 (27 : Fin 32) = tbl := by rw [u8.regs, g7_27]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x40, 0x4)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m8]; exact w7_2c
    have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m8]; exact w7_30
    have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m8]; exact w7_40
    have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m8]; exact w7_50
    have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m8]; exact w7_54
    have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m8]; exact w7_58
    have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m8]; exact w7_5c
    have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m8]; exact w7_60
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
    have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m8]; exact w7_68
    have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m8]; exact w7_6c
    have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m8]; exact w7_70
    have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
    have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m8]; exact w7_78
    have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m8]; exact w7_7c
    have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m8]; exact w7_80
    have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m8]; exact w7_84
    have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m8]; exact w7_88
    have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m8]; exact w7_8c
    have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m8]; exact w7_90
    have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m8]; exact w7_94
    have w8_98 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m8]; exact w7_98
    have w8_9c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m8]; exact w7_9c
    have w8_a0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m8]; exact w7_a0
    have w8_a4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m8]; exact w7_a4
    have w8_150 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m8]; exact w7_150
    have w8_154 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m8]; exact w7_154
    have w8_158 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m8]; exact w7_158
    have w8_15c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m8]; exact w7_15c
    clear w7_15c w7_158 w7_154 w7_150 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_40 w7_30 w7_2c g7_10 g7_27 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_11 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
    -- 0x942: sw
    obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sw F E8 s8 sv_at_942 (off' := 0x944) (c := 0x44)
      (by decide) (by rw [g8_2]; sv_addr) (by decide) (by decide)
    have t9 : Steps n0 n9 := t8.trans d9
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg9 (8 : Fin 32), g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = tbp := by rw [rg9 (9 : Fin 32), g8_9]
    have g9_10 : reg n9 a0 = BitVec.ofNat 32 0x6 := by rw [rg9 a0, g8_10]
    have g9_11 : reg n9 a1 = L := by rw [rg9 a1, g8_11]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rg9 (18 : Fin 32), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rg9 (19 : Fin 32), g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [rg9 (20 : Fin 32), g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [rg9 (21 : Fin 32), g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [rg9 (22 : Fin 32), g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = sgp := by rw [rg9 (23 : Fin 32), g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = kp := by rw [rg9 (24 : Fin 32), g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = sgl := by rw [rg9 (25 : Fin 32), g8_25]
    have g9_27 : reg n9 (27 : Fin 32) = tbl := by rw [rg9 (27 : Fin 32), g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x40, 0x4), (0x44, 0x4)] := keep_kk8.trans K9.toL
    clear keep_kk8
    have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K9.w32 (by decide) (by decide)).trans w8_2c
    have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K9.w32 (by decide) (by decide)).trans w8_30
    have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K9.w32 (by decide) (by decide)).trans w8_40
    have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K9.w32 (by decide) (by decide)).trans w8_50
    have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K9.w32 (by decide) (by decide)).trans w8_54
    have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K9.w32 (by decide) (by decide)).trans w8_58
    have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K9.w32 (by decide) (by decide)).trans w8_5c
    have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K9.w32 (by decide) (by decide)).trans w8_60
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K9.w32 (by decide) (by decide)).trans w8_64
    have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K9.w32 (by decide) (by decide)).trans w8_68
    have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K9.w32 (by decide) (by decide)).trans w8_6c
    have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K9.w32 (by decide) (by decide)).trans w8_70
    have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K9.w32 (by decide) (by decide)).trans w8_74
    have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K9.w32 (by decide) (by decide)).trans w8_78
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K9.w32 (by decide) (by decide)).trans w8_7c
    have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K9.w32 (by decide) (by decide)).trans w8_80
    have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K9.w32 (by decide) (by decide)).trans w8_84
    have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K9.w32 (by decide) (by decide)).trans w8_88
    have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K9.w32 (by decide) (by decide)).trans w8_8c
    have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K9.w32 (by decide) (by decide)).trans w8_90
    have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K9.w32 (by decide) (by decide)).trans w8_94
    have w9_98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K9.w32 (by decide) (by decide)).trans w8_98
    have w9_9c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K9.w32 (by decide) (by decide)).trans w8_9c
    have w9_a0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K9.w32 (by decide) (by decide)).trans w8_a0
    have w9_a4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K9.w32 (by decide) (by decide)).trans w8_a4
    have w9_150 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K9.w32 (by decide) (by decide)).trans w8_150
    have w9_154 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K9.w32 (by decide) (by decide)).trans w8_154
    have w9_158 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K9.w32 (by decide) (by decide)).trans w8_158
    have w9_15c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := (K9.w32 (by decide) (by decide)).trans w8_15c
    have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x6 := by rw [W9, g8_10]
    clear w8_15c w8_158 w8_154 w8_150 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_40 w8_30 w8_2c g8_27 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_11 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    -- 0x944: lw
    obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g9_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s10 : St n10.mem SV n10 0x946 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
    have g10_9 : reg n10 (9 : Fin 32) = tbp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_9]
    have g10_10 : reg n10 a0 = BitVec.ofNat 32 0x6 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_10]
    have g10_11 : reg n10 a1 = L := by rw [u10.regs, upd_ne (by decide) (by decide), g9_11]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = dg := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = rootp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = ll := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = sgp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = kp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = sgl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
    have g10_27 : reg n10 (27 : Fin 32) = tbl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
    have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x6 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g9_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w9_44]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x40, 0x4), (0x44, 0x4)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m10]; exact w9_2c
    have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m10]; exact w9_30
    have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m10]; exact w9_40
    have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x6 := by rw [m10]; exact w9_44
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
    have w10_15c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m10]; exact w9_15c
    clear w9_44 w9_15c w9_158 w9_154 w9_150 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_40 w9_30 w9_2c g9_27 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_11 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
    -- 0x946: j
    obtain ⟨n11, d11, u11⟩ := s10.jump E10.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s10.pc]; decide)
    have s11 : St n11.mem SV n11 0x7A4 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x6 := by rw [u11.regs, g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = tbp := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x6 := by rw [u11.regs, g10_10]
    have g11_11 : reg n11 a1 = L := by rw [u11.regs, g10_11]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = sgp := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = kp := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = sgl := by rw [u11.regs, g10_25]
    have g11_27 : reg n11 (27 : Fin 32) = tbl := by rw [u11.regs, g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x40, 0x4), (0x44, 0x4)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m11]; exact w10_2c
    have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m11]; exact w10_30
    have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m11]; exact w10_40
    have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x6 := by rw [m11]; exact w10_44
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
    have w11_15c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m11]; exact w10_15c
    clear w10_15c w10_158 w10_154 w10_150 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_44 w10_40 w10_30 w10_2c g10_8 g10_27 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_11 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hz_5 h0'), sv_fail F E11 s11 t11 (fun x hx => (fR11 x hx).trans (fM x hx).symm) V11 hret g11_2 g11_18 hO g11_3 g11_4 (by rw [g11_8]; sv_code)⟩
  -- 0x3C6: branch, not taken
  obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.self 0x3CA sv_at_3c6
    (by decide) (by rw [g5_11, g5_10]; exact br_bltu_f (by omega))
  have s6 : St n6.mem SV n6 0x3CA (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u6.regs, g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = tbp := by rw [u6.regs, g5_9]
  have g6_10 : reg n6 a0 = rem := by rw [u6.regs, g5_10]
  have g6_11 : reg n6 a1 = L := by rw [u6.regs, g5_11]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [u6.regs, g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [u6.regs, g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [u6.regs, g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = sgp := by rw [u6.regs, g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = kp := by rw [u6.regs, g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = sgl := by rw [u6.regs, g5_25]
  have g6_27 : reg n6 (27 : Fin 32) = tbl := by rw [u6.regs, g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x40, 0x4)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m6]; exact w5_2c
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m6]; exact w5_30
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m6]; exact w5_40
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
  have w6_15c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m6]; exact w5_15c
  clear w5_40 w5_15c w5_158 w5_154 w5_150 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_30 w5_2c g5_27 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_11 g5_10 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 rg5 W5 K5 fr5 s5 d5
  -- 0x3CA: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_3ca (off' := 0x3CE) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x150 = B + 0x21A0 + BitVec.ofNat 32 0x150 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0x3CE (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = tbp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_9]
  have g7_11 : reg n7 a1 = L := by rw [u7.regs, upd_ne (by decide) (by decide), g6_11]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = dg := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = rootp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = ll := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = sgp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = kp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = sgl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
  have g7_27 : reg n7 (27 : Fin 32) = tbl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
  have g7_10 : reg n7 a0 = p0 := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x150 = B + 0x21A0 + BitVec.ofNat 32 0x150 by sv_addr, w6_150]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x40, 0x4)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m7]; exact w6_2c
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m7]; exact w6_30
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m7]; exact w6_40
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m7]; exact w6_50
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m7]; exact w6_54
  have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m7]; exact w6_58
  have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m7]; exact w6_5c
  have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m7]; exact w6_60
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m7]; exact w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m7]; exact w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m7]; exact w6_70
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m7]; exact w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m7]; exact w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m7]; exact w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m7]; exact w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m7]; exact w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m7]; exact w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m7]; exact w6_8c
  have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m7]; exact w6_90
  have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m7]; exact w6_94
  have w7_98 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m7]; exact w6_98
  have w7_9c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m7]; exact w6_9c
  have w7_a0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m7]; exact w6_a0
  have w7_a4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m7]; exact w6_a4
  have w7_150 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m7]; exact w6_150
  have w7_154 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m7]; exact w6_154
  have w7_158 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m7]; exact w6_158
  have w7_15c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m7]; exact w6_15c
  clear w6_15c w6_158 w6_154 w6_150 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_40 w6_30 w6_2c g6_27 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x3CE: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_3ce (off' := 0x3D0) (c := 0x3C)
    (by decide) (by rw [g7_2]; sv_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg8 (8 : Fin 32), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = tbp := by rw [rg8 (9 : Fin 32), g7_9]
  have g8_10 : reg n8 a0 = p0 := by rw [rg8 a0, g7_10]
  have g8_11 : reg n8 a1 = L := by rw [rg8 a1, g7_11]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [rg8 (20 : Fin 32), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [rg8 (22 : Fin 32), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = sgp := by rw [rg8 (23 : Fin 32), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = kp := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = sgl := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_27 : reg n8 (27 : Fin 32) = tbl := by rw [rg8 (27 : Fin 32), g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x40, 0x4), (0x3C, 0x4)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K8.w32 (by decide) (by decide)).trans w7_2c
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K8.w32 (by decide) (by decide)).trans w7_30
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K8.w32 (by decide) (by decide)).trans w7_40
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
  have w8_15c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := (K8.w32 (by decide) (by decide)).trans w7_15c
  have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [W8, g7_10]
  clear w7_15c w7_158 w7_154 w7_150 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_40 w7_30 w7_2c g7_10 g7_27 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_11 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x3D0
  obtain ⟨n9, c9, u9⟩ := s8.block svX13d0 E8.self svX13d0_end
    ⟨trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0x3D6 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svX13d0 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
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
  have g9_10 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svX13d0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g9_11 : reg n9 a1 = B + 0x21A0 + BitVec.ofNat 32 0x150 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svX13d0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x40, 0x4), (0x3C, 0x4)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m9]; exact w8_2c
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m9]; exact w8_30
  have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m9]; exact w8_3c
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m9]; exact w8_40
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
  have w9_15c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem := by rw [m9]; exact w8_15c
  clear w8_3c w8_15c w8_158 w8_154 w8_150 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_40 w8_30 w8_2c g8_27 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_11 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0x3D6: sv_seqF
  obtain ⟨n10, c10, s10, sp10, rk10, K10, Ok10, Er10, fr10⟩ := sv_seqF (oc := 0x420) (dc := 0x150)
    F E9 s9 sv_at_3d6 sv_at_3da (by decide) (by decide) g9_2 g9_10 g9_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w9_158 w9_15c xl_in
  have t10 : Steps n0 n10 := t9.trans c10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keepL K10 (by decide)
  rw [sv_mb fR9 xl_in] at Ok10 Er10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rk10 sp (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk10 (3 : Fin 32) (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk10 (4 : Fin 32) (by decide) (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk10 (8 : Fin 32) (by decide) (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = tbp := by rw [rk10 (9 : Fin 32) (by decide) (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rk10 (18 : Fin 32) (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rk10 (19 : Fin 32) (by decide) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = dg := by rw [rk10 (20 : Fin 32) (by decide) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = rootp := by rw [rk10 (21 : Fin 32) (by decide) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = ll := by rw [rk10 (22 : Fin 32) (by decide) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = sgp := by rw [rk10 (23 : Fin 32) (by decide) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = kp := by rw [rk10 (24 : Fin 32) (by decide) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = sgl := by rw [rk10 (25 : Fin 32) (by decide) (by decide), g9_25]
  have g10_27 : reg n10 (27 : Fin 32) = tbl := by rw [rk10 (27 : Fin 32) (by decide) (by decide), g9_27]
  obtain ⟨r10, hr10⟩ : ∃ r, derElement 0x30 (memBytes M0 (cur) (rem).toNat) = r := ⟨_, rfl⟩
  rcases r10 with er10 | tl10
  · obtain ⟨z10, ez10⟩ := Er10 er10 hr10
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8)] := keep_kk9.trans K10
    clear keep_kk9
    have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K10.w32 (by decide) (by decide)).trans w9_2c
    have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K10.w32 (by decide) (by decide)).trans w9_30
    have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K10.w32 (by decide) (by decide)).trans w9_3c
    have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K10.w32 (by decide) (by decide)).trans w9_40
    have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K10.w32 (by decide) (by decide)).trans w9_50
    have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K10.w32 (by decide) (by decide)).trans w9_54
    have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K10.w32 (by decide) (by decide)).trans w9_58
    have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K10.w32 (by decide) (by decide)).trans w9_5c
    have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K10.w32 (by decide) (by decide)).trans w9_60
    have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K10.w32 (by decide) (by decide)).trans w9_64
    have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K10.w32 (by decide) (by decide)).trans w9_68
    have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K10.w32 (by decide) (by decide)).trans w9_6c
    have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K10.w32 (by decide) (by decide)).trans w9_70
    have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K10.w32 (by decide) (by decide)).trans w9_74
    have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K10.w32 (by decide) (by decide)).trans w9_78
    have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K10.w32 (by decide) (by decide)).trans w9_7c
    have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K10.w32 (by decide) (by decide)).trans w9_80
    have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K10.w32 (by decide) (by decide)).trans w9_84
    have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K10.w32 (by decide) (by decide)).trans w9_88
    have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K10.w32 (by decide) (by decide)).trans w9_8c
    have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K10.w32 (by decide) (by decide)).trans w9_90
    have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K10.w32 (by decide) (by decide)).trans w9_94
    have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K10.w32 (by decide) (by decide)).trans w9_98
    have w10_9c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K10.w32 (by decide) (by decide)).trans w9_9c
    have w10_a0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K10.w32 (by decide) (by decide)).trans w9_a0
    have w10_a4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K10.w32 (by decide) (by decide)).trans w9_a4
    have w10_150 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K10.w32 (by decide) (by decide)).trans w9_150
    have w10_154 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K10.w32 (by decide) (by decide)).trans w9_154
    have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z10
    have b10_424 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er10 := ez10
    clear w9_15c w9_158 w9_154 w9_150 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_40 w9_3c w9_30 w9_2c g9_11 g9_10 g9_27 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
    -- 0x3DE: lw
    obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_3de (off' := 0x3E2) (by decide)
      (by rw [g10_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s11 : St n11.mem SV n11 0x3E2 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = tbp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = sgp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = kp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = sgl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
    have g11_27 : reg n11 (27 : Fin 32) = tbl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
    have g11_26 : reg n11 (26 : Fin 32) = 0 := by
      rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g10_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w10_420]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m11]; exact w10_2c
    have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m11]; exact w10_30
    have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m11]; exact w10_3c
    have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m11]; exact w10_40
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
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m11]; exact w10_420
    have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er10 := by rw [m11]; exact b10_424
    clear b10_424 w10_420 w10_154 w10_150 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_40 w10_3c w10_30 w10_2c ez10 z10
    -- 0x3E2: lbu
    obtain ⟨n12, d12, u12⟩ := s11.lbu E11.self sv_at_3e2 (off' := 0x3E6) (by decide)
    have s12 : St n12.mem SV n12 0x3E6 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
    have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
    have g12_9 : reg n12 (9 : Fin 32) = tbp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = dg := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = rootp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = ll := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = sgp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = kp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = sgl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = 0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = tbl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
    have g12_10 : reg n12 a0 = (derErrByte er10).zeroExtend 32 := by
      rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g11_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b11_424]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m12]; exact w11_2c
    have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m12]; exact w11_30
    have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m12]; exact w11_3c
    have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m12]; exact w11_40
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
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m12]; exact w11_420
    have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er10 := by rw [m12]; exact b11_424
    clear b11_424 w11_420 w11_154 w11_150 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_40 w11_3c w11_30 w11_2c g11_26 g11_27 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    -- 0x3E6: sw
    obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := sv_sw F E12 s12 sv_at_3e6 (off' := 0x3E8) (c := 0x44)
      (by decide) (by rw [g12_2]; sv_addr) (by decide) (by decide)
    have t13 : Steps n0 n13 := t12.trans d13
    have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
    have E13 : SvCode n13.mem := E12.fr F fr13
    have V13 : SvSaves B n13.mem v := V12.keep K13 (by decide)
    have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
    have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
    have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
    have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg13 (8 : Fin 32), g12_8]
    have g13_9 : reg n13 (9 : Fin 32) = tbp := by rw [rg13 (9 : Fin 32), g12_9]
    have g13_10 : reg n13 a0 = (derErrByte er10).zeroExtend 32 := by rw [rg13 a0, g12_10]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rg13 (18 : Fin 32), g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rg13 (19 : Fin 32), g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = dg := by rw [rg13 (20 : Fin 32), g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = rootp := by rw [rg13 (21 : Fin 32), g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = ll := by rw [rg13 (22 : Fin 32), g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = sgp := by rw [rg13 (23 : Fin 32), g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = kp := by rw [rg13 (24 : Fin 32), g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = sgl := by rw [rg13 (25 : Fin 32), g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = 0 := by rw [rg13 (26 : Fin 32), g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = tbl := by rw [rg13 (27 : Fin 32), g12_27]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4)] := keep_kk12.trans K13.toL
    clear keep_kk12
    have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K13.w32 (by decide) (by decide)).trans w12_2c
    have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K13.w32 (by decide) (by decide)).trans w12_30
    have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K13.w32 (by decide) (by decide)).trans w12_3c
    have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K13.w32 (by decide) (by decide)).trans w12_40
    have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K13.w32 (by decide) (by decide)).trans w12_50
    have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K13.w32 (by decide) (by decide)).trans w12_54
    have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K13.w32 (by decide) (by decide)).trans w12_58
    have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K13.w32 (by decide) (by decide)).trans w12_5c
    have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K13.w32 (by decide) (by decide)).trans w12_60
    have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K13.w32 (by decide) (by decide)).trans w12_64
    have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K13.w32 (by decide) (by decide)).trans w12_68
    have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K13.w32 (by decide) (by decide)).trans w12_6c
    have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K13.w32 (by decide) (by decide)).trans w12_70
    have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K13.w32 (by decide) (by decide)).trans w12_74
    have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K13.w32 (by decide) (by decide)).trans w12_78
    have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K13.w32 (by decide) (by decide)).trans w12_7c
    have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K13.w32 (by decide) (by decide)).trans w12_80
    have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K13.w32 (by decide) (by decide)).trans w12_84
    have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K13.w32 (by decide) (by decide)).trans w12_88
    have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K13.w32 (by decide) (by decide)).trans w12_8c
    have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K13.w32 (by decide) (by decide)).trans w12_90
    have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K13.w32 (by decide) (by decide)).trans w12_94
    have w13_98 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K13.w32 (by decide) (by decide)).trans w12_98
    have w13_9c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K13.w32 (by decide) (by decide)).trans w12_9c
    have w13_a0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K13.w32 (by decide) (by decide)).trans w12_a0
    have w13_a4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K13.w32 (by decide) (by decide)).trans w12_a4
    have w13_150 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K13.w32 (by decide) (by decide)).trans w12_150
    have w13_154 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K13.w32 (by decide) (by decide)).trans w12_154
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K13.w32 (by decide) (by decide)).trans w12_420
    have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er10 := (K13.b8 (by decide) (by decide)).trans b12_424
    have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er10).zeroExtend 32 := by rw [W13, g12_10]
    clear b12_424 w12_420 w12_154 w12_150 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_40 w12_3c w12_30 w12_2c g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    -- 0x3E8: branch, taken
    obtain ⟨n14, d14, u14⟩ := s13.taken E13.self 0x944 sv_at_3e8
      (by decide) (by rw [g13_26, s13.zero]; rfl)
    have s14 : St n14.mem SV n14 0x944 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
    have t14 : Steps n0 n14 := t13.trans (.single d14)
    have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
    have E14 : SvCode n14.mem := E13.fr F fr14
    have V14 : SvSaves B n14.mem v := V13.same m14
    have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, g13_2]
    have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, g13_3]
    have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, g13_4]
    have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u14.regs, g13_8]
    have g14_9 : reg n14 (9 : Fin 32) = tbp := by rw [u14.regs, g13_9]
    have g14_10 : reg n14 a0 = (derErrByte er10).zeroExtend 32 := by rw [u14.regs, g13_10]
    have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, g13_19]
    have g14_20 : reg n14 (20 : Fin 32) = dg := by rw [u14.regs, g13_20]
    have g14_21 : reg n14 (21 : Fin 32) = rootp := by rw [u14.regs, g13_21]
    have g14_22 : reg n14 (22 : Fin 32) = ll := by rw [u14.regs, g13_22]
    have g14_23 : reg n14 (23 : Fin 32) = sgp := by rw [u14.regs, g13_23]
    have g14_24 : reg n14 (24 : Fin 32) = kp := by rw [u14.regs, g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = sgl := by rw [u14.regs, g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = 0 := by rw [u14.regs, g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = tbl := by rw [u14.regs, g13_27]
    have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4)] := by rw [m14]; exact keep_kk13
    clear keep_kk13
    have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m14]; exact w13_2c
    have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m14]; exact w13_30
    have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m14]; exact w13_3c
    have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m14]; exact w13_40
    have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er10).zeroExtend 32 := by rw [m14]; exact w13_44
    have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m14]; exact w13_50
    have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m14]; exact w13_54
    have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m14]; exact w13_58
    have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m14]; exact w13_5c
    have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m14]; exact w13_60
    have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m14]; exact w13_64
    have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m14]; exact w13_68
    have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m14]; exact w13_6c
    have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m14]; exact w13_70
    have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m14]; exact w13_74
    have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m14]; exact w13_78
    have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m14]; exact w13_7c
    have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m14]; exact w13_80
    have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m14]; exact w13_84
    have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m14]; exact w13_88
    have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m14]; exact w13_8c
    have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m14]; exact w13_90
    have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m14]; exact w13_94
    have w14_98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m14]; exact w13_98
    have w14_9c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m14]; exact w13_9c
    have w14_a0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m14]; exact w13_a0
    have w14_a4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m14]; exact w13_a4
    have w14_150 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m14]; exact w13_150
    have w14_154 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m14]; exact w13_154
    have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m14]; exact w13_420
    have b14_424 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er10 := by rw [m14]; exact b13_424
    clear w13_44 b13_424 w13_420 w13_154 w13_150 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_40 w13_3c w13_30 w13_2c g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
    -- 0x944: lw
    obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g14_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s15 : St n15.mem SV n15 0x946 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
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
    have g15_10 : reg n15 a0 = (derErrByte er10).zeroExtend 32 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_10]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
    have g15_20 : reg n15 (20 : Fin 32) = dg := by rw [u15.regs, upd_ne (by decide) (by decide), g14_20]
    have g15_21 : reg n15 (21 : Fin 32) = rootp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = ll := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = sgp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = kp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = sgl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = 0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = tbl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
    have g15_8 : reg n15 (8 : Fin 32) = (derErrByte er10).zeroExtend 32 := by
      rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g14_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w14_44]
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4)] := by rw [m15]; exact keep_kk14
    clear keep_kk14
    have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m15]; exact w14_2c
    have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m15]; exact w14_30
    have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m15]; exact w14_3c
    have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m15]; exact w14_40
    have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er10).zeroExtend 32 := by rw [m15]; exact w14_44
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
    have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m15]; exact w14_420
    have b15_424 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er10 := by rw [m15]; exact b14_424
    clear b14_424 w14_420 w14_154 w14_150 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_44 w14_40 w14_3c w14_30 w14_2c g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
    -- 0x946: j
    obtain ⟨n16, d16, u16⟩ := s15.jump E15.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s15.pc]; decide)
    have s16 : St n16.mem SV n16 0x7A4 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
    have g16_8 : reg n16 (8 : Fin 32) = (derErrByte er10).zeroExtend 32 := by rw [u16.regs, g15_8]
    have g16_9 : reg n16 (9 : Fin 32) = tbp := by rw [u16.regs, g15_9]
    have g16_10 : reg n16 a0 = (derErrByte er10).zeroExtend 32 := by rw [u16.regs, g15_10]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = dg := by rw [u16.regs, g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = rootp := by rw [u16.regs, g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = ll := by rw [u16.regs, g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = sgp := by rw [u16.regs, g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = kp := by rw [u16.regs, g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = sgl := by rw [u16.regs, g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = 0 := by rw [u16.regs, g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = tbl := by rw [u16.regs, g15_27]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m16]; exact w15_2c
    have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m16]; exact w15_30
    have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m16]; exact w15_3c
    have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m16]; exact w15_40
    have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er10).zeroExtend 32 := by rw [m16]; exact w15_44
    have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m16]; exact w15_50
    have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m16]; exact w15_54
    have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m16]; exact w15_58
    have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m16]; exact w15_5c
    have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m16]; exact w15_60
    have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m16]; exact w15_64
    have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m16]; exact w15_68
    have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m16]; exact w15_6c
    have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m16]; exact w15_70
    have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m16]; exact w15_74
    have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m16]; exact w15_78
    have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m16]; exact w15_7c
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m16]; exact w15_80
    have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m16]; exact w15_84
    have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m16]; exact w15_88
    have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m16]; exact w15_8c
    have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m16]; exact w15_90
    have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m16]; exact w15_94
    have w16_98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m16]; exact w15_98
    have w16_9c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m16]; exact w15_9c
    have w16_a0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m16]; exact w15_a0
    have w16_a4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m16]; exact w15_a4
    have w16_150 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m16]; exact w15_150
    have w16_154 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m16]; exact w15_154
    have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m16]; exact w15_420
    have b16_424 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er10 := by rw [m16]; exact b15_424
    clear b15_424 w15_420 w15_154 w15_150 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_44 w15_40 w15_3c w15_30 w15_2c g15_8 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_10 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
    exact .inl ⟨(fun ⟨h0', tl10', h1', _⟩ => by rw [hr10] at h1'; cases h1'), sv_fail F E16 s16 t16 (fun x hx => (fR16 x hx).trans (fM x hx).symm) V16 hret g16_2 g16_18 hO g16_3 g16_4 (by rw [g16_8]; sv_code)⟩
  obtain ⟨o0_10, o4_10, o8_10, o12_10, d8_10, d12_10⟩ := Ok10 tl10 hr10
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8)] := keep_kk9.trans K10
  clear keep_kk9
  have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K10.w32 (by decide) (by decide)).trans w9_2c
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K10.w32 (by decide) (by decide)).trans w9_30
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K10.w32 (by decide) (by decide)).trans w9_3c
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K10.w32 (by decide) (by decide)).trans w9_40
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K10.w32 (by decide) (by decide)).trans w9_50
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K10.w32 (by decide) (by decide)).trans w9_54
  have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K10.w32 (by decide) (by decide)).trans w9_58
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K10.w32 (by decide) (by decide)).trans w9_5c
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K10.w32 (by decide) (by decide)).trans w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K10.w32 (by decide) (by decide)).trans w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K10.w32 (by decide) (by decide)).trans w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K10.w32 (by decide) (by decide)).trans w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K10.w32 (by decide) (by decide)).trans w9_70
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K10.w32 (by decide) (by decide)).trans w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K10.w32 (by decide) (by decide)).trans w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K10.w32 (by decide) (by decide)).trans w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K10.w32 (by decide) (by decide)).trans w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K10.w32 (by decide) (by decide)).trans w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K10.w32 (by decide) (by decide)).trans w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K10.w32 (by decide) (by decide)).trans w9_8c
  have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K10.w32 (by decide) (by decide)).trans w9_90
  have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K10.w32 (by decide) (by decide)).trans w9_94
  have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K10.w32 (by decide) (by decide)).trans w9_98
  have w10_9c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K10.w32 (by decide) (by decide)).trans w9_9c
  have w10_a0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K10.w32 (by decide) (by decide)).trans w9_a0
  have w10_a4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K10.w32 (by decide) (by decide)).trans w9_a4
  have w10_150 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K10.w32 (by decide) (by decide)).trans w9_150
  have w10_154 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K10.w32 (by decide) (by decide)).trans w9_154
  have w10_158 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := d8_10
  have w10_15c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := d12_10
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cur) + BitVec.ofNat 32 tl10.header := o0_10
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := o4_10
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := o8_10
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := o12_10
  clear w9_15c w9_158 w9_154 w9_150 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_40 w9_3c w9_30 w9_2c g9_11 g9_10 g9_27 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x3DE: lw
  obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_3de (off' := 0x3E2) (by decide)
    (by rw [g10_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s11 : St n11.mem SV n11 0x3E2 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = tbp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = sgp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = kp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = sgl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
  have g11_27 : reg n11 (27 : Fin 32) = tbl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
  have g11_26 : reg n11 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g10_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w10_420]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m11]; exact w10_2c
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m11]; exact w10_30
  have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m11]; exact w10_3c
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m11]; exact w10_40
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
  have w11_158 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m11]; exact w10_158
  have w11_15c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m11]; exact w10_15c
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m11]; exact w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m11]; exact w10_42c
  clear w10_42c w10_428 w10_424 w10_420 w10_15c w10_158 w10_154 w10_150 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_40 w10_3c w10_30 w10_2c d12_10 d8_10 o12_10 o8_10 o4_10 o0_10 g10_27 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 Er10 Ok10 K10 rk10 sp10 s10 c10
  -- 0x3E2: lbu
  obtain ⟨n12, d12, u12⟩ := s11.lbu E11.self sv_at_3e2 (off' := 0x3E6) (by decide)
  have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by
    have h := byte_of_ld w11_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s12 : St n12.mem SV n12 0x3E6 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = tbp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = dg := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = rootp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = ll := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = sgp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = kp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = sgl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = tbl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_10 : reg n12 a0 = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b11_424]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m12]; exact w11_2c
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m12]; exact w11_30
  have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m12]; exact w11_3c
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m12]; exact w11_40
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
  have w12_158 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m12]; exact w11_158
  have w12_15c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m12]; exact w11_15c
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m12]; exact w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m12]; exact w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m12]; exact w11_42c
  have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m12]; exact b11_424
  clear w11_42c w11_428 w11_424 w11_420 w11_15c w11_158 w11_154 w11_150 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_40 w11_3c w11_30 w11_2c g11_26 g11_27 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x3E6: sw
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := sv_sw F E12 s12 sv_at_3e6 (off' := 0x3E8) (c := 0x44)
    (by decide) (by rw [g12_2]; sv_addr) (by decide) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg13 (8 : Fin 32), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = tbp := by rw [rg13 (9 : Fin 32), g12_9]
  have g13_10 : reg n13 a0 = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg13 a0, g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rg13 (18 : Fin 32), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rg13 (19 : Fin 32), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = dg := by rw [rg13 (20 : Fin 32), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = rootp := by rw [rg13 (21 : Fin 32), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = ll := by rw [rg13 (22 : Fin 32), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = sgp := by rw [rg13 (23 : Fin 32), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = kp := by rw [rg13 (24 : Fin 32), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = sgl := by rw [rg13 (25 : Fin 32), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [rg13 (26 : Fin 32), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = tbl := by rw [rg13 (27 : Fin 32), g12_27]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K13.w32 (by decide) (by decide)).trans w12_2c
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K13.w32 (by decide) (by decide)).trans w12_30
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K13.w32 (by decide) (by decide)).trans w12_3c
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K13.w32 (by decide) (by decide)).trans w12_40
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K13.w32 (by decide) (by decide)).trans w12_50
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K13.w32 (by decide) (by decide)).trans w12_54
  have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K13.w32 (by decide) (by decide)).trans w12_58
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K13.w32 (by decide) (by decide)).trans w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K13.w32 (by decide) (by decide)).trans w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K13.w32 (by decide) (by decide)).trans w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K13.w32 (by decide) (by decide)).trans w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K13.w32 (by decide) (by decide)).trans w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K13.w32 (by decide) (by decide)).trans w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K13.w32 (by decide) (by decide)).trans w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K13.w32 (by decide) (by decide)).trans w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K13.w32 (by decide) (by decide)).trans w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K13.w32 (by decide) (by decide)).trans w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K13.w32 (by decide) (by decide)).trans w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K13.w32 (by decide) (by decide)).trans w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K13.w32 (by decide) (by decide)).trans w12_8c
  have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K13.w32 (by decide) (by decide)).trans w12_90
  have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K13.w32 (by decide) (by decide)).trans w12_94
  have w13_98 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K13.w32 (by decide) (by decide)).trans w12_98
  have w13_9c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K13.w32 (by decide) (by decide)).trans w12_9c
  have w13_a0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K13.w32 (by decide) (by decide)).trans w12_a0
  have w13_a4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K13.w32 (by decide) (by decide)).trans w12_a4
  have w13_150 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K13.w32 (by decide) (by decide)).trans w12_150
  have w13_154 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K13.w32 (by decide) (by decide)).trans w12_154
  have w13_158 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K13.w32 (by decide) (by decide)).trans w12_158
  have w13_15c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K13.w32 (by decide) (by decide)).trans w12_15c
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cur) + BitVec.ofNat 32 tl10.header := (K13.w32 (by decide) (by decide)).trans w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := (K13.w32 (by decide) (by decide)).trans w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := (K13.w32 (by decide) (by decide)).trans w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K13.w32 (by decide) (by decide)).trans w12_42c
  have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K13.b8 (by decide) (by decide)).trans b12_424
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [W13, g12_10]
  clear b12_424 w12_42c w12_428 w12_424 w12_420 w12_15c w12_158 w12_154 w12_150 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_40 w12_3c w12_30 w12_2c g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 b11_424 u12 d12
  -- 0x3E8: branch, not taken
  obtain ⟨n14, d14, u14⟩ := s13.notTaken E13.self 0x3EC sv_at_3e8
    (by decide) (by rw [g13_26, s13.zero]; exact br_beq_f (xl_in.ok_ne hr10))
  have s14 : St n14.mem SV n14 0x3EC (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u14.regs, g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = tbp := by rw [u14.regs, g13_9]
  have g14_10 : reg n14 a0 = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [u14.regs, g13_10]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = dg := by rw [u14.regs, g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = rootp := by rw [u14.regs, g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = ll := by rw [u14.regs, g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = sgp := by rw [u14.regs, g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = kp := by rw [u14.regs, g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = sgl := by rw [u14.regs, g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u14.regs, g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = tbl := by rw [u14.regs, g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m14]; exact w13_2c
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m14]; exact w13_30
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m14]; exact w13_3c
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m14]; exact w13_40
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m14]; exact w13_44
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m14]; exact w13_50
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m14]; exact w13_54
  have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m14]; exact w13_58
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m14]; exact w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m14]; exact w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m14]; exact w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m14]; exact w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m14]; exact w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m14]; exact w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m14]; exact w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m14]; exact w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m14]; exact w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m14]; exact w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m14]; exact w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m14]; exact w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m14]; exact w13_8c
  have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m14]; exact w13_90
  have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m14]; exact w13_94
  have w14_98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m14]; exact w13_98
  have w14_9c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m14]; exact w13_9c
  have w14_a0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m14]; exact w13_a0
  have w14_a4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m14]; exact w13_a4
  have w14_150 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m14]; exact w13_150
  have w14_154 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m14]; exact w13_154
  have w14_158 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m14]; exact w13_158
  have w14_15c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m14]; exact w13_15c
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m14]; exact w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m14]; exact w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m14]; exact w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m14]; exact w13_42c
  have b14_424 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m14]; exact b13_424
  clear w13_44 b13_424 w13_42c w13_428 w13_424 w13_420 w13_15c w13_158 w13_154 w13_150 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_40 w13_3c w13_30 w13_2c g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  -- 0x3EC
  obtain ⟨n15, c15, u15⟩ := s14.block svX13ec E14.self svX13ec_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem SV n15 0x3F6 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock svX13ec (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by
    rw [rb15, runBlock_reg _ _ _ sp s14.zero (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (3 : Fin 32) s14.zero (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (4 : Fin 32) s14.zero (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb15, runBlock_reg _ _ _ (8 : Fin 32) s14.zero (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = tbp := by
    rw [rb15, runBlock_reg _ _ _ (9 : Fin 32) s14.zero (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by
    rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by
    rw [rb15, runBlock_reg _ _ _ (19 : Fin 32) s14.zero (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = dg := by
    rw [rb15, runBlock_reg _ _ _ (20 : Fin 32) s14.zero (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = rootp := by
    rw [rb15, runBlock_reg _ _ _ (21 : Fin 32) s14.zero (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = ll := by
    rw [rb15, runBlock_reg _ _ _ (22 : Fin 32) s14.zero (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = sgp := by
    rw [rb15, runBlock_reg _ _ _ (23 : Fin 32) s14.zero (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = kp := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = sgl := by
    rw [rb15, runBlock_reg _ _ _ (25 : Fin 32) s14.zero (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = tbl := by
    rw [rb15, runBlock_reg _ _ _ (27 : Fin 32) s14.zero (by decide), g14_27]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0x405 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svX13ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_10, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g15_11 : reg n15 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svX13ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_10, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g15_12 : reg n15 a2 = BitVec.ofNat 32 0xB := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svX13ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_10, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m15]; exact w14_2c
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m15]; exact w14_30
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m15]; exact w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m15]; exact w14_40
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m15]; exact w14_44
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
  have w15_158 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m15]; exact w14_158
  have w15_15c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m15]; exact w14_15c
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m15]; exact w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m15]; exact w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m15]; exact w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m15]; exact w14_42c
  have b15_424 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m15]; exact b14_424
  clear b14_424 w14_42c w14_428 w14_424 w14_420 w14_15c w14_158 w14_154 w14_150 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_44 w14_40 w14_3c w14_30 w14_2c g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  have b15_425 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by
    have h := byte_of_ld w15_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b15_426 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by
    have h := byte_of_ld w15_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b15_427 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by
    have h := byte_of_ld w15_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0x3F6: memcpy
  obtain ⟨n16, P16, K16, X16⟩ := sv_mc (c := 0x405) (d := 0x425) (N := 0xB) F E15 s15 sv_at_3f6 sv_at_3fa
    (by decide) (by decide) g15_2 g15_10 g15_11 g15_12
    (by decide) (by decide) (by decide)
  have s16 := P16.st
  have fr16 := P16.fr
  have t16 : Steps n0 n16 := t15.trans P16.steps
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [P16.regs sp (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P16.regs (3 : Fin 32) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P16.regs (4 : Fin 32) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [P16.regs (8 : Fin 32) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = tbp := by rw [P16.regs (9 : Fin 32) (by decide), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [P16.regs (18 : Fin 32) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [P16.regs (19 : Fin 32) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = dg := by rw [P16.regs (20 : Fin 32) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = rootp := by rw [P16.regs (21 : Fin 32) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = ll := by rw [P16.regs (22 : Fin 32) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = sgp := by rw [P16.regs (23 : Fin 32) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = kp := by rw [P16.regs (24 : Fin 32) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = sgl := by rw [P16.regs (25 : Fin 32) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [P16.regs (26 : Fin 32) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = tbl := by rw [P16.regs (27 : Fin 32) (by decide), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K16.w32 (by decide) (by decide)).trans w15_2c
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K16.w32 (by decide) (by decide)).trans w15_30
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K16.w32 (by decide) (by decide)).trans w15_3c
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K16.w32 (by decide) (by decide)).trans w15_40
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := (K16.w32 (by decide) (by decide)).trans w15_44
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
  have w16_158 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K16.w32 (by decide) (by decide)).trans w15_158
  have w16_15c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K16.w32 (by decide) (by decide)).trans w15_15c
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cur) + BitVec.ofNat 32 tl10.header := (K16.w32 (by decide) (by decide)).trans w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := (K16.w32 (by decide) (by decide)).trans w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := (K16.w32 (by decide) (by decide)).trans w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K16.w32 (by decide) (by decide)).trans w15_42c
  have b16_424 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K16.b8 (by decide) (by decide)).trans b15_424
  have b16_425 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K16.b8 (by decide) (by decide)).trans b15_425
  have b16_426 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K16.b8 (by decide) (by decide)).trans b15_426
  have b16_427 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K16.b8 (by decide) (by decide)).trans b15_427
  have w16_408 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (cur) + BitVec.ofNat 32 tl10.header := by
    rw [← w15_428]
    exact ld_cp fun q hq => by
      have := X16 (0x3 + q) (by omega)
      rwa [show 0x405 + (0x3 + q) = 0x408 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w16_40c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl10.len := by
    rw [← w15_42c]
    exact ld_cp fun q hq => by
      have := X16 (0x7 + q) (by omega)
      rwa [show 0x405 + (0x7 + q) = 0x40C + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b16_405 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [show 0x405 = 0x405 + 0x0 from rfl, X16 0x0 (by decide)]; exact b15_425
  have b16_406 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [show 0x406 = 0x405 + 0x1 from rfl, X16 0x1 (by decide)]; exact b15_426
  have b16_407 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [show 0x407 = 0x405 + 0x2 from rfl, X16 0x2 (by decide)]; exact b15_427
  clear b15_424 w15_42c w15_428 w15_424 w15_420 w15_15c w15_158 w15_154 w15_150 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_44 w15_40 w15_3c w15_30 w15_2c g15_12 g15_11 g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  -- 0x3FE: sw
  obtain ⟨n17, d17, s17, fr17, K17, W17, rg17⟩ := sv_sw F E16 s16 sv_at_3fe (off' := 0x402) (c := 0x400)
    (by decide) (by rw [g16_2]; sv_addr) (by decide) (by decide)
  have t17 : Steps n0 n17 := t16.trans d17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rg17 sp, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg17 (3 : Fin 32), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg17 (4 : Fin 32), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg17 (8 : Fin 32), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = tbp := by rw [rg17 (9 : Fin 32), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [rg17 (18 : Fin 32), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [rg17 (19 : Fin 32), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [rg17 (20 : Fin 32), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [rg17 (21 : Fin 32), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [rg17 (22 : Fin 32), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = sgp := by rw [rg17 (23 : Fin 32), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = kp := by rw [rg17 (24 : Fin 32), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = sgl := by rw [rg17 (25 : Fin 32), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [rg17 (26 : Fin 32), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = tbl := by rw [rg17 (27 : Fin 32), g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K17.w32 (by decide) (by decide)).trans w16_2c
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K17.w32 (by decide) (by decide)).trans w16_30
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K17.w32 (by decide) (by decide)).trans w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K17.w32 (by decide) (by decide)).trans w16_40
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := (K17.w32 (by decide) (by decide)).trans w16_44
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K17.w32 (by decide) (by decide)).trans w16_50
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K17.w32 (by decide) (by decide)).trans w16_54
  have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K17.w32 (by decide) (by decide)).trans w16_58
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K17.w32 (by decide) (by decide)).trans w16_5c
  have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K17.w32 (by decide) (by decide)).trans w16_60
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K17.w32 (by decide) (by decide)).trans w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K17.w32 (by decide) (by decide)).trans w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K17.w32 (by decide) (by decide)).trans w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K17.w32 (by decide) (by decide)).trans w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K17.w32 (by decide) (by decide)).trans w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K17.w32 (by decide) (by decide)).trans w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K17.w32 (by decide) (by decide)).trans w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K17.w32 (by decide) (by decide)).trans w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K17.w32 (by decide) (by decide)).trans w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K17.w32 (by decide) (by decide)).trans w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K17.w32 (by decide) (by decide)).trans w16_8c
  have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K17.w32 (by decide) (by decide)).trans w16_90
  have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K17.w32 (by decide) (by decide)).trans w16_94
  have w17_98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K17.w32 (by decide) (by decide)).trans w16_98
  have w17_9c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K17.w32 (by decide) (by decide)).trans w16_9c
  have w17_a0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K17.w32 (by decide) (by decide)).trans w16_a0
  have w17_a4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K17.w32 (by decide) (by decide)).trans w16_a4
  have w17_150 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K17.w32 (by decide) (by decide)).trans w16_150
  have w17_154 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K17.w32 (by decide) (by decide)).trans w16_154
  have w17_158 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K17.w32 (by decide) (by decide)).trans w16_158
  have w17_15c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K17.w32 (by decide) (by decide)).trans w16_15c
  have w17_408 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (cur) + BitVec.ofNat 32 tl10.header := (K17.w32 (by decide) (by decide)).trans w16_408
  have w17_40c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl10.len := (K17.w32 (by decide) (by decide)).trans w16_40c
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cur) + BitVec.ofNat 32 tl10.header := (K17.w32 (by decide) (by decide)).trans w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := (K17.w32 (by decide) (by decide)).trans w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := (K17.w32 (by decide) (by decide)).trans w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K17.w32 (by decide) (by decide)).trans w16_42c
  have b17_405 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K17.b8 (by decide) (by decide)).trans b16_405
  have b17_406 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K17.b8 (by decide) (by decide)).trans b16_406
  have b17_407 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K17.b8 (by decide) (by decide)).trans b16_407
  have b17_424 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K17.b8 (by decide) (by decide)).trans b16_424
  have b17_425 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K17.b8 (by decide) (by decide)).trans b16_425
  have b17_426 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K17.b8 (by decide) (by decide)).trans b16_426
  have b17_427 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K17.b8 (by decide) (by decide)).trans b16_427
  have w17_400 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [W17, g16_26]
  clear b16_407 b16_406 b16_405 w16_40c w16_408 b16_427 b16_426 b16_425 b16_424 w16_42c w16_428 w16_424 w16_420 w16_15c w16_158 w16_154 w16_150 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_44 w16_40 w16_3c w16_30 w16_2c g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 s16 X16 K16 P16 b15_427 b15_426 b15_425
  -- 0x402: lw
  obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_402 (off' := 0x404) (by decide)
    (by rw [g17_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s18 : St n18.mem SV n18 0x404 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = tbp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [u18.regs, upd_ne (by decide) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = sgp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = kp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = sgl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = tbl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
  have g18_10 : reg n18 a0 = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g17_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w17_44]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m18]; exact w17_2c
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m18]; exact w17_30
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m18]; exact w17_3c
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m18]; exact w17_40
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m18]; exact w17_44
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
  have w18_158 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m18]; exact w17_158
  have w18_15c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m18]; exact w17_15c
  have w18_400 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m18]; exact w17_400
  have w18_408 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m18]; exact w17_408
  have w18_40c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl10.len := by rw [m18]; exact w17_40c
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m18]; exact w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m18]; exact w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m18]; exact w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m18]; exact w17_42c
  have b18_405 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m18]; exact b17_405
  have b18_406 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m18]; exact b17_406
  have b18_407 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m18]; exact b17_407
  have b18_424 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m18]; exact b17_424
  have b18_425 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m18]; exact b17_425
  have b18_426 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m18]; exact b17_426
  have b18_427 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m18]; exact b17_427
  clear w17_400 b17_427 b17_426 b17_425 b17_424 b17_407 b17_406 b17_405 w17_42c w17_428 w17_424 w17_420 w17_40c w17_408 w17_15c w17_158 w17_154 w17_150 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_44 w17_40 w17_3c w17_30 w17_2c g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
  -- 0x404: sb
  obtain ⟨n19, d19, s19, fr19, K19, W19, rg19⟩ := sv_sb F E18 s18 sv_at_404 (off' := 0x408) (c := 0x404)
    (by decide) (by rw [g18_2]; sv_addr) (by decide)
  have t19 : Steps n0 n19 := t18.trans d19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keep K19 (by decide)
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [rg19 sp, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg19 (3 : Fin 32), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg19 (4 : Fin 32), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg19 (8 : Fin 32), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = tbp := by rw [rg19 (9 : Fin 32), g18_9]
  have g19_10 : reg n19 a0 = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg19 a0, g18_10]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rg19 (18 : Fin 32), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rg19 (19 : Fin 32), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = dg := by rw [rg19 (20 : Fin 32), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = rootp := by rw [rg19 (21 : Fin 32), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = ll := by rw [rg19 (22 : Fin 32), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = sgp := by rw [rg19 (23 : Fin 32), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = kp := by rw [rg19 (24 : Fin 32), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = sgl := by rw [rg19 (25 : Fin 32), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [rg19 (26 : Fin 32), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = tbl := by rw [rg19 (27 : Fin 32), g18_27]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := keep_kk18.trans K19.toL
  clear keep_kk18
  have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K19.w32 (by decide) (by decide)).trans w18_2c
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K19.w32 (by decide) (by decide)).trans w18_30
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K19.w32 (by decide) (by decide)).trans w18_3c
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K19.w32 (by decide) (by decide)).trans w18_40
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := (K19.w32 (by decide) (by decide)).trans w18_44
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K19.w32 (by decide) (by decide)).trans w18_50
  have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K19.w32 (by decide) (by decide)).trans w18_54
  have w19_58 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K19.w32 (by decide) (by decide)).trans w18_58
  have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K19.w32 (by decide) (by decide)).trans w18_5c
  have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K19.w32 (by decide) (by decide)).trans w18_60
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K19.w32 (by decide) (by decide)).trans w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K19.w32 (by decide) (by decide)).trans w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K19.w32 (by decide) (by decide)).trans w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K19.w32 (by decide) (by decide)).trans w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K19.w32 (by decide) (by decide)).trans w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K19.w32 (by decide) (by decide)).trans w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K19.w32 (by decide) (by decide)).trans w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K19.w32 (by decide) (by decide)).trans w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K19.w32 (by decide) (by decide)).trans w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K19.w32 (by decide) (by decide)).trans w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K19.w32 (by decide) (by decide)).trans w18_8c
  have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K19.w32 (by decide) (by decide)).trans w18_90
  have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K19.w32 (by decide) (by decide)).trans w18_94
  have w19_98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K19.w32 (by decide) (by decide)).trans w18_98
  have w19_9c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K19.w32 (by decide) (by decide)).trans w18_9c
  have w19_a0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K19.w32 (by decide) (by decide)).trans w18_a0
  have w19_a4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K19.w32 (by decide) (by decide)).trans w18_a4
  have w19_150 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K19.w32 (by decide) (by decide)).trans w18_150
  have w19_154 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K19.w32 (by decide) (by decide)).trans w18_154
  have w19_158 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K19.w32 (by decide) (by decide)).trans w18_158
  have w19_15c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K19.w32 (by decide) (by decide)).trans w18_15c
  have w19_400 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := (K19.w32 (by decide) (by decide)).trans w18_400
  have w19_408 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (cur) + BitVec.ofNat 32 tl10.header := (K19.w32 (by decide) (by decide)).trans w18_408
  have w19_40c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl10.len := (K19.w32 (by decide) (by decide)).trans w18_40c
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cur) + BitVec.ofNat 32 tl10.header := (K19.w32 (by decide) (by decide)).trans w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := (K19.w32 (by decide) (by decide)).trans w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := (K19.w32 (by decide) (by decide)).trans w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K19.w32 (by decide) (by decide)).trans w18_42c
  have b19_405 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K19.b8 (by decide) (by decide)).trans b18_405
  have b19_406 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K19.b8 (by decide) (by decide)).trans b18_406
  have b19_407 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K19.b8 (by decide) (by decide)).trans b18_407
  have b19_424 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_424
  have b19_425 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K19.b8 (by decide) (by decide)).trans b18_425
  have b19_426 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K19.b8 (by decide) (by decide)).trans b18_426
  have b19_427 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K19.b8 (by decide) (by decide)).trans b18_427
  have b19_404 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [W19, g18_10, lbu_low]
  clear b18_427 b18_426 b18_425 b18_424 b18_407 b18_406 b18_405 w18_42c w18_428 w18_424 w18_420 w18_40c w18_408 w18_400 w18_15c w18_158 w18_154 w18_150 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_44 w18_40 w18_3c w18_30 w18_2c g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x408
  obtain ⟨n20, c20, u20⟩ := s19.block svX1408 E19.self svX1408_end
    ⟨trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x410 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svX1408 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
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
  have g20_26 : reg n20 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = tbl := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svX1408, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_11 : reg n20 a1 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svX1408, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m20]; exact w19_2c
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m20]; exact w19_30
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m20]; exact w19_3c
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m20]; exact w19_40
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m20]; exact w19_44
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
  have w20_158 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m20]; exact w19_158
  have w20_15c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m20]; exact w19_15c
  have w20_400 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_400
  have w20_408 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_408
  have w20_40c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl10.len := by rw [m20]; exact w19_40c
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl10.len := by rw [m20]; exact w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m20]; exact w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m20]; exact w19_42c
  have b20_404 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m20]; exact b19_404
  have b20_405 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m20]; exact b19_405
  have b20_406 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m20]; exact b19_406
  have b20_407 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m20]; exact b19_407
  have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m20]; exact b19_424
  have b20_425 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m20]; exact b19_425
  have b20_426 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m20]; exact b19_426
  have b20_427 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m20]; exact b19_427
  clear b19_404 b19_427 b19_426 b19_425 b19_424 b19_407 b19_406 b19_405 w19_42c w19_428 w19_424 w19_420 w19_40c w19_408 w19_400 w19_15c w19_158 w19_154 w19_150 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_44 w19_40 w19_3c w19_30 w19_2c g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 rg19 W19 K19 fr19 s19 d19
  -- 0x410: sv_oidF
  obtain ⟨n21, c21, s21, sp21, rk21, K21, A21, Ok21, Er21, fr21⟩ := sv_oidF (oc := 0x420) (dc := 0x400)
    F E20 s20 sv_at_410 sv_at_414 (by decide) (by decide) g20_2 g20_10 g20_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w20_408 w20_40c (xl_in.contentW hr10)
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keepL K21 (by decide)
  rw [sv_mb fR20 (xl_in.contentW hr10)] at A21 Ok21 Er21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rk21 sp (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk21 (3 : Fin 32) (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk21 (4 : Fin 32) (by decide) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk21 (8 : Fin 32) (by decide) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = tbp := by rw [rk21 (9 : Fin 32) (by decide) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rk21 (18 : Fin 32) (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rk21 (19 : Fin 32) (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = dg := by rw [rk21 (20 : Fin 32) (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = rootp := by rw [rk21 (21 : Fin 32) (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = ll := by rw [rk21 (22 : Fin 32) (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = sgp := by rw [rk21 (23 : Fin 32) (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = kp := by rw [rk21 (24 : Fin 32) (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = sgl := by rw [rk21 (25 : Fin 32) (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [rk21 (26 : Fin 32) (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = tbl := by rw [rk21 (27 : Fin 32) (by decide) (by decide), g20_27]
  obtain ⟨r21, hr21⟩ : ∃ r, derContent ((cur) + BitVec.ofNat 32 tl10.header) (derOid (memBytes M0 ((cur) + BitVec.ofNat 32 tl10.header) (BitVec.ofNat 32 tl10.len).toNat)) = r := ⟨_, rfl⟩
  rcases r21 with er21 | ⟨op21, ol21⟩
  · obtain ⟨z21, ez21⟩ := Er21 er21 hr21
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8)] := keep_kk20.trans K21
    clear keep_kk20
    have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K21.w32 (by decide) (by decide)).trans w20_2c
    have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K21.w32 (by decide) (by decide)).trans w20_30
    have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K21.w32 (by decide) (by decide)).trans w20_3c
    have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K21.w32 (by decide) (by decide)).trans w20_40
    have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := (K21.w32 (by decide) (by decide)).trans w20_44
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
    have w21_158 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K21.w32 (by decide) (by decide)).trans w20_158
    have w21_15c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K21.w32 (by decide) (by decide)).trans w20_15c
    have w21_400 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := (K21.w32 (by decide) (by decide)).trans w20_400
    have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := (K21.w32 (by decide) (by decide)).trans w20_428
    have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K21.w32 (by decide) (by decide)).trans w20_42c
    have b21_404 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K21.b8 (by decide) (by decide)).trans b20_404
    have b21_405 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K21.b8 (by decide) (by decide)).trans b20_405
    have b21_406 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K21.b8 (by decide) (by decide)).trans b20_406
    have b21_407 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K21.b8 (by decide) (by decide)).trans b20_407
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z21
    have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := ez21
    clear b20_427 b20_426 b20_425 b20_424 b20_407 b20_406 b20_405 b20_404 w20_42c w20_428 w20_424 w20_420 w20_40c w20_408 w20_400 w20_15c w20_158 w20_154 w20_150 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_44 w20_40 w20_3c w20_30 w20_2c g20_11 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
    -- 0x418: lw
    obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_418 (off' := 0x41C) (by decide)
      (by rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s22 : St n22.mem SV n22 0x41C (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = tbp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = sgp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = kp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = sgl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = tbl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
    have g22_10 : reg n22 a0 = 0 := by
      rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w21_420]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m22]; exact w21_2c
    have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m22]; exact w21_30
    have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m22]; exact w21_3c
    have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m22]; exact w21_40
    have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m22]; exact w21_44
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
    have w22_158 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m22]; exact w21_158
    have w22_15c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m22]; exact w21_15c
    have w22_400 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m22]; exact w21_400
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m22]; exact w21_420
    have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m22]; exact w21_428
    have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m22]; exact w21_42c
    have b22_404 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m22]; exact b21_404
    have b22_405 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m22]; exact b21_405
    have b22_406 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m22]; exact b21_406
    have b22_407 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m22]; exact b21_407
    have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := by rw [m22]; exact b21_424
    clear b21_424 w21_420 b21_407 b21_406 b21_405 b21_404 w21_42c w21_428 w21_400 w21_15c w21_158 w21_154 w21_150 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_44 w21_40 w21_3c w21_30 w21_2c ez21 z21
    -- 0x41C: sw
    obtain ⟨n23, d23, s23, fr23, K23, W23, rg23⟩ := sv_sw F E22 s22 sv_at_41c (off' := 0x41E) (c := 0x4C)
      (by decide) (by rw [g22_2]; sv_addr) (by decide) (by decide)
    have t23 : Steps n0 n23 := t22.trans d23
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.keep K23 (by decide)
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [rg23 sp, g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg23 (3 : Fin 32), g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg23 (4 : Fin 32), g22_4]
    have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg23 (8 : Fin 32), g22_8]
    have g23_9 : reg n23 (9 : Fin 32) = tbp := by rw [rg23 (9 : Fin 32), g22_9]
    have g23_10 : reg n23 a0 = 0 := by rw [rg23 a0, g22_10]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [rg23 (18 : Fin 32), g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [rg23 (19 : Fin 32), g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = dg := by rw [rg23 (20 : Fin 32), g22_20]
    have g23_21 : reg n23 (21 : Fin 32) = rootp := by rw [rg23 (21 : Fin 32), g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = ll := by rw [rg23 (22 : Fin 32), g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = sgp := by rw [rg23 (23 : Fin 32), g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = kp := by rw [rg23 (24 : Fin 32), g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = sgl := by rw [rg23 (25 : Fin 32), g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [rg23 (26 : Fin 32), g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = tbl := by rw [rg23 (27 : Fin 32), g22_27]
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4)] := keep_kk22.trans K23.toL
    clear keep_kk22
    have w23_2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K23.w32 (by decide) (by decide)).trans w22_2c
    have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K23.w32 (by decide) (by decide)).trans w22_30
    have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K23.w32 (by decide) (by decide)).trans w22_3c
    have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K23.w32 (by decide) (by decide)).trans w22_40
    have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := (K23.w32 (by decide) (by decide)).trans w22_44
    have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K23.w32 (by decide) (by decide)).trans w22_50
    have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K23.w32 (by decide) (by decide)).trans w22_54
    have w23_58 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K23.w32 (by decide) (by decide)).trans w22_58
    have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K23.w32 (by decide) (by decide)).trans w22_5c
    have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K23.w32 (by decide) (by decide)).trans w22_60
    have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K23.w32 (by decide) (by decide)).trans w22_64
    have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K23.w32 (by decide) (by decide)).trans w22_68
    have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K23.w32 (by decide) (by decide)).trans w22_6c
    have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K23.w32 (by decide) (by decide)).trans w22_70
    have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K23.w32 (by decide) (by decide)).trans w22_74
    have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K23.w32 (by decide) (by decide)).trans w22_78
    have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K23.w32 (by decide) (by decide)).trans w22_7c
    have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K23.w32 (by decide) (by decide)).trans w22_80
    have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K23.w32 (by decide) (by decide)).trans w22_84
    have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K23.w32 (by decide) (by decide)).trans w22_88
    have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K23.w32 (by decide) (by decide)).trans w22_8c
    have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K23.w32 (by decide) (by decide)).trans w22_90
    have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K23.w32 (by decide) (by decide)).trans w22_94
    have w23_98 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K23.w32 (by decide) (by decide)).trans w22_98
    have w23_9c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K23.w32 (by decide) (by decide)).trans w22_9c
    have w23_a0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K23.w32 (by decide) (by decide)).trans w22_a0
    have w23_a4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K23.w32 (by decide) (by decide)).trans w22_a4
    have w23_150 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K23.w32 (by decide) (by decide)).trans w22_150
    have w23_154 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K23.w32 (by decide) (by decide)).trans w22_154
    have w23_158 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K23.w32 (by decide) (by decide)).trans w22_158
    have w23_15c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K23.w32 (by decide) (by decide)).trans w22_15c
    have w23_400 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := (K23.w32 (by decide) (by decide)).trans w22_400
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K23.w32 (by decide) (by decide)).trans w22_420
    have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := (K23.w32 (by decide) (by decide)).trans w22_428
    have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K23.w32 (by decide) (by decide)).trans w22_42c
    have b23_404 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K23.b8 (by decide) (by decide)).trans b22_404
    have b23_405 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K23.b8 (by decide) (by decide)).trans b22_405
    have b23_406 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K23.b8 (by decide) (by decide)).trans b22_406
    have b23_407 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K23.b8 (by decide) (by decide)).trans b22_407
    have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := (K23.b8 (by decide) (by decide)).trans b22_424
    have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = 0 := by rw [W23, g22_10]
    clear b22_424 b22_407 b22_406 b22_405 b22_404 w22_42c w22_428 w22_420 w22_400 w22_15c w22_158 w22_154 w22_150 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_44 w22_40 w22_3c w22_30 w22_2c g22_10 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    -- 0x41E: branch, taken
    obtain ⟨n24, d24, u24⟩ := s23.taken E23.self 0x7F2 sv_at_41e
      (by decide) (by rw [g23_10, s23.zero]; rfl)
    have s24 : St n24.mem SV n24 0x7F2 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
    have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u24.regs, g23_8]
    have g24_9 : reg n24 (9 : Fin 32) = tbp := by rw [u24.regs, g23_9]
    have g24_10 : reg n24 a0 = 0 := by rw [u24.regs, g23_10]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = dg := by rw [u24.regs, g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = rootp := by rw [u24.regs, g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = ll := by rw [u24.regs, g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = sgp := by rw [u24.regs, g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = kp := by rw [u24.regs, g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = sgl := by rw [u24.regs, g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u24.regs, g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = tbl := by rw [u24.regs, g23_27]
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m24]; exact w23_2c
    have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m24]; exact w23_30
    have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m24]; exact w23_3c
    have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m24]; exact w23_40
    have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m24]; exact w23_44
    have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = 0 := by rw [m24]; exact w23_4c
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
    have w24_158 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m24]; exact w23_158
    have w24_15c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m24]; exact w23_15c
    have w24_400 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m24]; exact w23_400
    have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m24]; exact w23_420
    have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m24]; exact w23_428
    have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m24]; exact w23_42c
    have b24_404 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m24]; exact b23_404
    have b24_405 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m24]; exact b23_405
    have b24_406 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m24]; exact b23_406
    have b24_407 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m24]; exact b23_407
    have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := by rw [m24]; exact b23_424
    clear w23_4c b23_424 b23_407 b23_406 b23_405 b23_404 w23_42c w23_428 w23_420 w23_400 w23_15c w23_158 w23_154 w23_150 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_44 w23_40 w23_3c w23_30 w23_2c g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 rg23 W23 K23 fr23 s23 d23
    -- 0x7F2: lbu
    obtain ⟨n25, d25, u25⟩ := s24.lbu E24.self sv_at_7f2 (off' := 0x7F6) (by decide)
    have s25 : St n25.mem SV n25 0x7F6 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
    have m25 : n25.mem = n24.mem := u25.mem
    have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
    have t25 : Steps n0 n25 := t24.trans (.single d25)
    have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
    have E25 : SvCode n25.mem := E24.fr F fr25
    have V25 : SvSaves B n25.mem v := V24.same m25
    have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
    have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
    have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
    have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_8]
    have g25_9 : reg n25 (9 : Fin 32) = tbp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_9]
    have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
    have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
    have g25_20 : reg n25 (20 : Fin 32) = dg := by rw [u25.regs, upd_ne (by decide) (by decide), g24_20]
    have g25_21 : reg n25 (21 : Fin 32) = rootp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
    have g25_22 : reg n25 (22 : Fin 32) = ll := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
    have g25_23 : reg n25 (23 : Fin 32) = sgp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
    have g25_24 : reg n25 (24 : Fin 32) = kp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_24]
    have g25_25 : reg n25 (25 : Fin 32) = sgl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
    have g25_26 : reg n25 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
    have g25_27 : reg n25 (27 : Fin 32) = tbl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
    have g25_10 : reg n25 a0 = (derErrByte er21).zeroExtend 32 := by
      rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g24_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b24_424]
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4)] := by rw [m25]; exact keep_kk24
    clear keep_kk24
    have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m25]; exact w24_2c
    have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m25]; exact w24_30
    have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m25]; exact w24_3c
    have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m25]; exact w24_40
    have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m25]; exact w24_44
    have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = 0 := by rw [m25]; exact w24_4c
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
    have w25_158 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m25]; exact w24_158
    have w25_15c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m25]; exact w24_15c
    have w25_400 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m25]; exact w24_400
    have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m25]; exact w24_420
    have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m25]; exact w24_428
    have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m25]; exact w24_42c
    have b25_404 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m25]; exact b24_404
    have b25_405 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m25]; exact b24_405
    have b25_406 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m25]; exact b24_406
    have b25_407 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m25]; exact b24_407
    have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := by rw [m25]; exact b24_424
    clear b24_424 b24_407 b24_406 b24_405 b24_404 w24_42c w24_428 w24_420 w24_400 w24_15c w24_158 w24_154 w24_150 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_44 w24_40 w24_3c w24_30 w24_2c g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
    -- 0x7F6: j
    obtain ⟨n26, d26, u26⟩ := s25.jump E25.self sv_at_7f6 (off' := 0x942) (by decide)
      (by rw [s25.pc]; decide)
    have s26 : St n26.mem SV n26 0x942 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans (.single d26)
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u26.regs, g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = tbp := by rw [u26.regs, g25_9]
    have g26_10 : reg n26 a0 = (derErrByte er21).zeroExtend 32 := by rw [u26.regs, g25_10]
    have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, g25_19]
    have g26_20 : reg n26 (20 : Fin 32) = dg := by rw [u26.regs, g25_20]
    have g26_21 : reg n26 (21 : Fin 32) = rootp := by rw [u26.regs, g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = ll := by rw [u26.regs, g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = sgp := by rw [u26.regs, g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = kp := by rw [u26.regs, g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = sgl := by rw [u26.regs, g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u26.regs, g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = tbl := by rw [u26.regs, g25_27]
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4)] := by rw [m26]; exact keep_kk25
    clear keep_kk25
    have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m26]; exact w25_2c
    have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m26]; exact w25_30
    have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m26]; exact w25_3c
    have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m26]; exact w25_40
    have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m26]; exact w25_44
    have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = 0 := by rw [m26]; exact w25_4c
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
    have w26_158 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m26]; exact w25_158
    have w26_15c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m26]; exact w25_15c
    have w26_400 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m26]; exact w25_400
    have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m26]; exact w25_420
    have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m26]; exact w25_428
    have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m26]; exact w25_42c
    have b26_404 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m26]; exact b25_404
    have b26_405 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m26]; exact b25_405
    have b26_406 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m26]; exact b25_406
    have b26_407 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m26]; exact b25_407
    have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := by rw [m26]; exact b25_424
    clear b25_424 b25_407 b25_406 b25_405 b25_404 w25_42c w25_428 w25_420 w25_400 w25_15c w25_158 w25_154 w25_150 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_44 w25_40 w25_3c w25_30 w25_2c g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
    -- 0x942: sw
    obtain ⟨n27, d27, s27, fr27, K27, W27, rg27⟩ := sv_sw F E26 s26 sv_at_942 (off' := 0x944) (c := 0x44)
      (by decide) (by rw [g26_2]; sv_addr) (by decide) (by decide)
    have t27 : Steps n0 n27 := t26.trans d27
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.keep K27 (by decide)
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rg27 sp, g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg27 (3 : Fin 32), g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg27 (4 : Fin 32), g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg27 (8 : Fin 32), g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = tbp := by rw [rg27 (9 : Fin 32), g26_9]
    have g27_10 : reg n27 a0 = (derErrByte er21).zeroExtend 32 := by rw [rg27 a0, g26_10]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rg27 (18 : Fin 32), g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rg27 (19 : Fin 32), g26_19]
    have g27_20 : reg n27 (20 : Fin 32) = dg := by rw [rg27 (20 : Fin 32), g26_20]
    have g27_21 : reg n27 (21 : Fin 32) = rootp := by rw [rg27 (21 : Fin 32), g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = ll := by rw [rg27 (22 : Fin 32), g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = sgp := by rw [rg27 (23 : Fin 32), g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = kp := by rw [rg27 (24 : Fin 32), g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = sgl := by rw [rg27 (25 : Fin 32), g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [rg27 (26 : Fin 32), g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = tbl := by rw [rg27 (27 : Fin 32), g26_27]
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4), (0x44, 0x4)] := keep_kk26.trans K27.toL
    clear keep_kk26
    have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K27.w32 (by decide) (by decide)).trans w26_2c
    have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K27.w32 (by decide) (by decide)).trans w26_30
    have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K27.w32 (by decide) (by decide)).trans w26_3c
    have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K27.w32 (by decide) (by decide)).trans w26_40
    have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = 0 := (K27.w32 (by decide) (by decide)).trans w26_4c
    have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K27.w32 (by decide) (by decide)).trans w26_50
    have w27_54 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K27.w32 (by decide) (by decide)).trans w26_54
    have w27_58 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K27.w32 (by decide) (by decide)).trans w26_58
    have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K27.w32 (by decide) (by decide)).trans w26_5c
    have w27_60 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K27.w32 (by decide) (by decide)).trans w26_60
    have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K27.w32 (by decide) (by decide)).trans w26_64
    have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K27.w32 (by decide) (by decide)).trans w26_68
    have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K27.w32 (by decide) (by decide)).trans w26_6c
    have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K27.w32 (by decide) (by decide)).trans w26_70
    have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K27.w32 (by decide) (by decide)).trans w26_74
    have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K27.w32 (by decide) (by decide)).trans w26_78
    have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K27.w32 (by decide) (by decide)).trans w26_7c
    have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K27.w32 (by decide) (by decide)).trans w26_80
    have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K27.w32 (by decide) (by decide)).trans w26_84
    have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K27.w32 (by decide) (by decide)).trans w26_88
    have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K27.w32 (by decide) (by decide)).trans w26_8c
    have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K27.w32 (by decide) (by decide)).trans w26_90
    have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K27.w32 (by decide) (by decide)).trans w26_94
    have w27_98 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K27.w32 (by decide) (by decide)).trans w26_98
    have w27_9c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K27.w32 (by decide) (by decide)).trans w26_9c
    have w27_a0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K27.w32 (by decide) (by decide)).trans w26_a0
    have w27_a4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K27.w32 (by decide) (by decide)).trans w26_a4
    have w27_150 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K27.w32 (by decide) (by decide)).trans w26_150
    have w27_154 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K27.w32 (by decide) (by decide)).trans w26_154
    have w27_158 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K27.w32 (by decide) (by decide)).trans w26_158
    have w27_15c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K27.w32 (by decide) (by decide)).trans w26_15c
    have w27_400 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := (K27.w32 (by decide) (by decide)).trans w26_400
    have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K27.w32 (by decide) (by decide)).trans w26_420
    have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := (K27.w32 (by decide) (by decide)).trans w26_428
    have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K27.w32 (by decide) (by decide)).trans w26_42c
    have b27_404 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_404
    have b27_405 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K27.b8 (by decide) (by decide)).trans b26_405
    have b27_406 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K27.b8 (by decide) (by decide)).trans b26_406
    have b27_407 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K27.b8 (by decide) (by decide)).trans b26_407
    have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := (K27.b8 (by decide) (by decide)).trans b26_424
    have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er21).zeroExtend 32 := by rw [W27, g26_10]
    clear b26_424 b26_407 b26_406 b26_405 b26_404 w26_42c w26_428 w26_420 w26_400 w26_15c w26_158 w26_154 w26_150 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_44 w26_40 w26_3c w26_30 w26_2c g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
    -- 0x944: lw
    obtain ⟨n28, d28, u28⟩ := s27.lw E27.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g27_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s28 : St n28.mem SV n28 0x946 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_4]
    have g28_9 : reg n28 (9 : Fin 32) = tbp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_9]
    have g28_10 : reg n28 a0 = (derErrByte er21).zeroExtend 32 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_10]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, upd_ne (by decide) (by decide), g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = dg := by rw [u28.regs, upd_ne (by decide) (by decide), g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = rootp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = ll := by rw [u28.regs, upd_ne (by decide) (by decide), g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = sgp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = kp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = sgl := by rw [u28.regs, upd_ne (by decide) (by decide), g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u28.regs, upd_ne (by decide) (by decide), g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = tbl := by rw [u28.regs, upd_ne (by decide) (by decide), g27_27]
    have g28_8 : reg n28 (8 : Fin 32) = (derErrByte er21).zeroExtend 32 := by
      rw [u28.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g27_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w27_44]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4), (0x44, 0x4)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m28]; exact w27_2c
    have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m28]; exact w27_30
    have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m28]; exact w27_3c
    have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m28]; exact w27_40
    have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er21).zeroExtend 32 := by rw [m28]; exact w27_44
    have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = 0 := by rw [m28]; exact w27_4c
    have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := by rw [m28]; exact w27_50
    have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m28]; exact w27_54
    have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m28]; exact w27_58
    have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m28]; exact w27_5c
    have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m28]; exact w27_60
    have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m28]; exact w27_64
    have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m28]; exact w27_68
    have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m28]; exact w27_6c
    have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m28]; exact w27_70
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m28]; exact w27_74
    have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m28]; exact w27_78
    have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m28]; exact w27_7c
    have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m28]; exact w27_80
    have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m28]; exact w27_84
    have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m28]; exact w27_88
    have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m28]; exact w27_8c
    have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m28]; exact w27_90
    have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m28]; exact w27_94
    have w28_98 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m28]; exact w27_98
    have w28_9c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m28]; exact w27_9c
    have w28_a0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m28]; exact w27_a0
    have w28_a4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m28]; exact w27_a4
    have w28_150 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m28]; exact w27_150
    have w28_154 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m28]; exact w27_154
    have w28_158 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m28]; exact w27_158
    have w28_15c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m28]; exact w27_15c
    have w28_400 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m28]; exact w27_400
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m28]; exact w27_420
    have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m28]; exact w27_428
    have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m28]; exact w27_42c
    have b28_404 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m28]; exact b27_404
    have b28_405 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m28]; exact b27_405
    have b28_406 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m28]; exact b27_406
    have b28_407 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m28]; exact b27_407
    have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := by rw [m28]; exact b27_424
    clear w27_44 b27_424 b27_407 b27_406 b27_405 b27_404 w27_42c w27_428 w27_420 w27_400 w27_15c w27_158 w27_154 w27_150 w27_a4 w27_a0 w27_9c w27_98 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_40 w27_3c w27_30 w27_2c g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 rg27 W27 K27 fr27 s27 d27
    -- 0x946: j
    obtain ⟨n29, d29, u29⟩ := s28.jump E28.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s28.pc]; decide)
    have s29 : St n29.mem SV n29 0x7A4 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = (derErrByte er21).zeroExtend 32 := by rw [u29.regs, g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = tbp := by rw [u29.regs, g28_9]
    have g29_10 : reg n29 a0 = (derErrByte er21).zeroExtend 32 := by rw [u29.regs, g28_10]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = dg := by rw [u29.regs, g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = rootp := by rw [u29.regs, g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = ll := by rw [u29.regs, g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = sgp := by rw [u29.regs, g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = kp := by rw [u29.regs, g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = sgl := by rw [u29.regs, g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u29.regs, g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = tbl := by rw [u29.regs, g28_27]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4), (0x44, 0x4)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m29]; exact w28_2c
    have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m29]; exact w28_30
    have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m29]; exact w28_3c
    have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m29]; exact w28_40
    have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er21).zeroExtend 32 := by rw [m29]; exact w28_44
    have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = 0 := by rw [m29]; exact w28_4c
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
    have w29_158 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m29]; exact w28_158
    have w29_15c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m29]; exact w28_15c
    have w29_400 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m29]; exact w28_400
    have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m29]; exact w28_420
    have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m29]; exact w28_428
    have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m29]; exact w28_42c
    have b29_404 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m29]; exact b28_404
    have b29_405 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m29]; exact b28_405
    have b29_406 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m29]; exact b28_406
    have b29_407 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m29]; exact b28_407
    have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := by rw [m29]; exact b28_424
    clear b28_424 b28_407 b28_406 b28_405 b28_404 w28_42c w28_428 w28_420 w28_400 w28_15c w28_158 w28_154 w28_150 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_44 w28_40 w28_3c w28_30 w28_2c g28_8 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
    exact .inl ⟨(fun ⟨h0', tl10', h1', op21', ol21', h2', _⟩ => by rw [hr10] at h1'; cases h1'; rw [hr21] at h2'; cases h2'), sv_fail F E29 s29 t29 (fun x hx => (fR29 x hx).trans (fM x hx).symm) V29 hret g29_2 g29_18 hO g29_3 g29_4 (by rw [g29_8]; sv_code)⟩
  obtain ⟨to21, ht21, -, -⟩ := oid_ok_content hr21
  obtain ⟨p0_21, p4_21⟩ := Ok21 op21 ol21 hr21
  obtain ⟨d8_21, d12_21⟩ := A21 to21 (derOid_ok_elem ht21)
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8)] := keep_kk20.trans K21
  clear keep_kk20
  have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K21.w32 (by decide) (by decide)).trans w20_2c
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K21.w32 (by decide) (by decide)).trans w20_30
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K21.w32 (by decide) (by decide)).trans w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K21.w32 (by decide) (by decide)).trans w20_40
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := (K21.w32 (by decide) (by decide)).trans w20_44
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
  have w21_158 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K21.w32 (by decide) (by decide)).trans w20_158
  have w21_15c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K21.w32 (by decide) (by decide)).trans w20_15c
  have w21_400 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := (K21.w32 (by decide) (by decide)).trans w20_400
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := (K21.w32 (by decide) (by decide)).trans w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K21.w32 (by decide) (by decide)).trans w20_42c
  have b21_404 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K21.b8 (by decide) (by decide)).trans b20_404
  have b21_405 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K21.b8 (by decide) (by decide)).trans b20_405
  have b21_406 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K21.b8 (by decide) (by decide)).trans b20_406
  have b21_407 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K21.b8 (by decide) (by decide)).trans b20_407
  have w21_408 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((cur) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (to21.header + to21.len) := d8_21
  have w21_40c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) := d12_21
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op21 := p0_21
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol21 := p4_21
  clear b20_427 b20_426 b20_425 b20_424 b20_407 b20_406 b20_405 b20_404 w20_42c w20_428 w20_424 w20_420 w20_40c w20_408 w20_400 w20_15c w20_158 w20_154 w20_150 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_44 w20_40 w20_3c w20_30 w20_2c g20_11 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x418: lw
  obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_418 (off' := 0x41C) (by decide)
    (by rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s22 : St n22.mem SV n22 0x41C (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = tbp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = sgp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = kp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = sgl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = tbl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
  have g22_10 : reg n22 a0 = op21 := by
    rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w21_420]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m22]; exact w21_2c
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m22]; exact w21_30
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m22]; exact w21_3c
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m22]; exact w21_40
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m22]; exact w21_44
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
  have w22_158 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m22]; exact w21_158
  have w22_15c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m22]; exact w21_15c
  have w22_400 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m22]; exact w21_400
  have w22_408 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((cur) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (to21.header + to21.len) := by rw [m22]; exact w21_408
  have w22_40c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) := by rw [m22]; exact w21_40c
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op21 := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol21 := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m22]; exact w21_42c
  have b22_404 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m22]; exact b21_404
  have b22_405 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m22]; exact b21_405
  have b22_406 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m22]; exact b21_406
  have b22_407 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m22]; exact b21_407
  clear w21_424 w21_420 w21_40c w21_408 b21_407 b21_406 b21_405 b21_404 w21_42c w21_428 w21_400 w21_15c w21_158 w21_154 w21_150 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_44 w21_40 w21_3c w21_30 w21_2c d12_21 d8_21 p4_21 p0_21 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 Er21 Ok21 A21 K21 rk21 sp21 s21 c21
  -- 0x41C: sw
  obtain ⟨n23, d23, s23, fr23, K23, W23, rg23⟩ := sv_sw F E22 s22 sv_at_41c (off' := 0x41E) (c := 0x4C)
    (by decide) (by rw [g22_2]; sv_addr) (by decide) (by decide)
  have t23 : Steps n0 n23 := t22.trans d23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.keep K23 (by decide)
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [rg23 sp, g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg23 (3 : Fin 32), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg23 (4 : Fin 32), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg23 (8 : Fin 32), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = tbp := by rw [rg23 (9 : Fin 32), g22_9]
  have g23_10 : reg n23 a0 = op21 := by rw [rg23 a0, g22_10]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [rg23 (18 : Fin 32), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [rg23 (19 : Fin 32), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = dg := by rw [rg23 (20 : Fin 32), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = rootp := by rw [rg23 (21 : Fin 32), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = ll := by rw [rg23 (22 : Fin 32), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = sgp := by rw [rg23 (23 : Fin 32), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = kp := by rw [rg23 (24 : Fin 32), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = sgl := by rw [rg23 (25 : Fin 32), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [rg23 (26 : Fin 32), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = tbl := by rw [rg23 (27 : Fin 32), g22_27]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4)] := keep_kk22.trans K23.toL
  clear keep_kk22
  have w23_2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K23.w32 (by decide) (by decide)).trans w22_2c
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K23.w32 (by decide) (by decide)).trans w22_30
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K23.w32 (by decide) (by decide)).trans w22_3c
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K23.w32 (by decide) (by decide)).trans w22_40
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := (K23.w32 (by decide) (by decide)).trans w22_44
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K23.w32 (by decide) (by decide)).trans w22_50
  have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K23.w32 (by decide) (by decide)).trans w22_54
  have w23_58 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K23.w32 (by decide) (by decide)).trans w22_58
  have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K23.w32 (by decide) (by decide)).trans w22_5c
  have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K23.w32 (by decide) (by decide)).trans w22_60
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K23.w32 (by decide) (by decide)).trans w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K23.w32 (by decide) (by decide)).trans w22_68
  have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K23.w32 (by decide) (by decide)).trans w22_6c
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K23.w32 (by decide) (by decide)).trans w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K23.w32 (by decide) (by decide)).trans w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K23.w32 (by decide) (by decide)).trans w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K23.w32 (by decide) (by decide)).trans w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K23.w32 (by decide) (by decide)).trans w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K23.w32 (by decide) (by decide)).trans w22_84
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K23.w32 (by decide) (by decide)).trans w22_88
  have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K23.w32 (by decide) (by decide)).trans w22_8c
  have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K23.w32 (by decide) (by decide)).trans w22_90
  have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K23.w32 (by decide) (by decide)).trans w22_94
  have w23_98 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K23.w32 (by decide) (by decide)).trans w22_98
  have w23_9c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K23.w32 (by decide) (by decide)).trans w22_9c
  have w23_a0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K23.w32 (by decide) (by decide)).trans w22_a0
  have w23_a4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K23.w32 (by decide) (by decide)).trans w22_a4
  have w23_150 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K23.w32 (by decide) (by decide)).trans w22_150
  have w23_154 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K23.w32 (by decide) (by decide)).trans w22_154
  have w23_158 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K23.w32 (by decide) (by decide)).trans w22_158
  have w23_15c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K23.w32 (by decide) (by decide)).trans w22_15c
  have w23_400 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := (K23.w32 (by decide) (by decide)).trans w22_400
  have w23_408 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((cur) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (to21.header + to21.len) := (K23.w32 (by decide) (by decide)).trans w22_408
  have w23_40c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) := (K23.w32 (by decide) (by decide)).trans w22_40c
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op21 := (K23.w32 (by decide) (by decide)).trans w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol21 := (K23.w32 (by decide) (by decide)).trans w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := (K23.w32 (by decide) (by decide)).trans w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K23.w32 (by decide) (by decide)).trans w22_42c
  have b23_404 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K23.b8 (by decide) (by decide)).trans b22_404
  have b23_405 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K23.b8 (by decide) (by decide)).trans b22_405
  have b23_406 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K23.b8 (by decide) (by decide)).trans b22_406
  have b23_407 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K23.b8 (by decide) (by decide)).trans b22_407
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op21 := by rw [W23, g22_10]
  clear b22_407 b22_406 b22_405 b22_404 w22_42c w22_428 w22_424 w22_420 w22_40c w22_408 w22_400 w22_15c w22_158 w22_154 w22_150 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_44 w22_40 w22_3c w22_30 w22_2c g22_10 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0x41E: branch, not taken
  obtain ⟨n24, d24, u24⟩ := s23.notTaken E23.self 0x422 sv_at_41e
    (by decide) (by rw [g23_10, s23.zero]; exact br_beq_f (((xl_in.contentW hr10).oidIn hr21).pos_ne))
  have s24 : St n24.mem SV n24 0x422 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u24.regs, g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = tbp := by rw [u24.regs, g23_9]
  have g24_10 : reg n24 a0 = op21 := by rw [u24.regs, g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = dg := by rw [u24.regs, g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = rootp := by rw [u24.regs, g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = ll := by rw [u24.regs, g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = sgp := by rw [u24.regs, g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = kp := by rw [u24.regs, g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = sgl := by rw [u24.regs, g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u24.regs, g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = tbl := by rw [u24.regs, g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m24]; exact w23_2c
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m24]; exact w23_30
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m24]; exact w23_3c
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m24]; exact w23_40
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m24]; exact w23_44
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op21 := by rw [m24]; exact w23_4c
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
  have w24_158 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m24]; exact w23_158
  have w24_15c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m24]; exact w23_15c
  have w24_400 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m24]; exact w23_400
  have w24_408 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((cur) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (to21.header + to21.len) := by rw [m24]; exact w23_408
  have w24_40c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) := by rw [m24]; exact w23_40c
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op21 := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol21 := by rw [m24]; exact w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m24]; exact w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m24]; exact w23_42c
  have b24_404 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m24]; exact b23_404
  have b24_405 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m24]; exact b23_405
  have b24_406 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m24]; exact b23_406
  have b24_407 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m24]; exact b23_407
  clear w23_4c b23_407 b23_406 b23_405 b23_404 w23_42c w23_428 w23_424 w23_420 w23_40c w23_408 w23_400 w23_15c w23_158 w23_154 w23_150 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_44 w23_40 w23_3c w23_30 w23_2c g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 rg23 W23 K23 fr23 s23 d23
  -- 0x422: lw
  obtain ⟨n25, d25, u25⟩ := s24.lw E24.self sv_at_422 (off' := 0x426) (by decide)
    (by rw [g24_2, show B + 0x21A0 + 0x40C = B + 0x21A0 + BitVec.ofNat 32 0x40C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s25 : St n25.mem SV n25 0x426 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans (.single d25)
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = tbp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = dg := by rw [u25.regs, upd_ne (by decide) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = rootp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = ll := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = sgp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = kp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = sgl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = tbl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
  have g25_10 : reg n25 a0 = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) := by
    rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g24_2, show B + 0x21A0 + 0x40C = B + 0x21A0 + BitVec.ofNat 32 0x40C by sv_addr, w24_40c]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m25]; exact w24_2c
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m25]; exact w24_30
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m25]; exact w24_3c
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m25]; exact w24_40
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m25]; exact w24_44
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op21 := by rw [m25]; exact w24_4c
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
  have w25_158 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m25]; exact w24_158
  have w25_15c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m25]; exact w24_15c
  have w25_400 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m25]; exact w24_400
  have w25_408 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((cur) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (to21.header + to21.len) := by rw [m25]; exact w24_408
  have w25_40c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) := by rw [m25]; exact w24_40c
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op21 := by rw [m25]; exact w24_420
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol21 := by rw [m25]; exact w24_424
  have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m25]; exact w24_428
  have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m25]; exact w24_42c
  have b25_404 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m25]; exact b24_404
  have b25_405 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m25]; exact b24_405
  have b25_406 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m25]; exact b24_406
  have b25_407 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m25]; exact b24_407
  clear b24_407 b24_406 b24_405 b24_404 w24_42c w24_428 w24_424 w24_420 w24_40c w24_408 w24_400 w24_15c w24_158 w24_154 w24_150 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_44 w24_40 w24_3c w24_30 w24_2c g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x426: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_426 (off' := 0x42A) (by decide)
    (by rw [g25_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0x42A (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = tbp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
  have g26_10 : reg n26 a0 = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_10]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = dg := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = rootp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = ll := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = sgp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = kp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = sgl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = tbl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_11 : reg n26 a1 = ol21 := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w25_424]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m26]; exact w25_2c
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m26]; exact w25_30
  have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := by rw [m26]; exact w25_3c
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := by rw [m26]; exact w25_40
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := by rw [m26]; exact w25_44
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op21 := by rw [m26]; exact w25_4c
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
  have w26_158 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m26]; exact w25_158
  have w26_15c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := by rw [m26]; exact w25_15c
  have w26_400 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m26]; exact w25_400
  have w26_408 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((cur) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (to21.header + to21.len) := by rw [m26]; exact w25_408
  have w26_40c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) := by rw [m26]; exact w25_40c
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op21 := by rw [m26]; exact w25_420
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol21 := by rw [m26]; exact w25_424
  have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := by rw [m26]; exact w25_428
  have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := by rw [m26]; exact w25_42c
  have b26_404 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := by rw [m26]; exact b25_404
  have b26_405 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := by rw [m26]; exact b25_405
  have b26_406 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := by rw [m26]; exact b25_406
  have b26_407 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := by rw [m26]; exact b25_407
  clear b25_407 b25_406 b25_405 b25_404 w25_42c w25_428 w25_424 w25_420 w25_40c w25_408 w25_400 w25_15c w25_158 w25_154 w25_150 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_44 w25_40 w25_3c w25_30 w25_2c g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
  -- 0x42A: sw
  obtain ⟨n27, d27, s27, fr27, K27, W27, rg27⟩ := sv_sw F E26 s26 sv_at_42a (off' := 0x42C) (c := 0x48)
    (by decide) (by rw [g26_2]; sv_addr) (by decide) (by decide)
  have t27 : Steps n0 n27 := t26.trans d27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keep K27 (by decide)
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rg27 sp, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg27 (3 : Fin 32), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg27 (4 : Fin 32), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg27 (8 : Fin 32), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = tbp := by rw [rg27 (9 : Fin 32), g26_9]
  have g27_10 : reg n27 a0 = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) := by rw [rg27 a0, g26_10]
  have g27_11 : reg n27 a1 = ol21 := by rw [rg27 a1, g26_11]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rg27 (18 : Fin 32), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rg27 (19 : Fin 32), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = dg := by rw [rg27 (20 : Fin 32), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = rootp := by rw [rg27 (21 : Fin 32), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = ll := by rw [rg27 (22 : Fin 32), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = sgp := by rw [rg27 (23 : Fin 32), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = kp := by rw [rg27 (24 : Fin 32), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = sgl := by rw [rg27 (25 : Fin 32), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = (cur) + BitVec.ofNat 32 tl10.header := by rw [rg27 (26 : Fin 32), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = tbl := by rw [rg27 (27 : Fin 32), g26_27]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4), (0x48, 0x4)] := keep_kk26.trans K27.toL
  clear keep_kk26
  have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K27.w32 (by decide) (by decide)).trans w26_2c
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K27.w32 (by decide) (by decide)).trans w26_30
  have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 := (K27.w32 (by decide) (by decide)).trans w26_3c
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L := (K27.w32 (by decide) (by decide)).trans w26_40
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((BitVec.ofNat 32 tl10.len).extractLsb' 0 8).zeroExtend 32 := (K27.w32 (by decide) (by decide)).trans w26_44
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op21 := (K27.w32 (by decide) (by decide)).trans w26_4c
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem := (K27.w32 (by decide) (by decide)).trans w26_50
  have w27_54 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K27.w32 (by decide) (by decide)).trans w26_54
  have w27_58 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K27.w32 (by decide) (by decide)).trans w26_58
  have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K27.w32 (by decide) (by decide)).trans w26_5c
  have w27_60 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K27.w32 (by decide) (by decide)).trans w26_60
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K27.w32 (by decide) (by decide)).trans w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K27.w32 (by decide) (by decide)).trans w26_68
  have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K27.w32 (by decide) (by decide)).trans w26_6c
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K27.w32 (by decide) (by decide)).trans w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K27.w32 (by decide) (by decide)).trans w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K27.w32 (by decide) (by decide)).trans w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K27.w32 (by decide) (by decide)).trans w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K27.w32 (by decide) (by decide)).trans w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K27.w32 (by decide) (by decide)).trans w26_84
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K27.w32 (by decide) (by decide)).trans w26_88
  have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K27.w32 (by decide) (by decide)).trans w26_8c
  have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K27.w32 (by decide) (by decide)).trans w26_90
  have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K27.w32 (by decide) (by decide)).trans w26_94
  have w27_98 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K27.w32 (by decide) (by decide)).trans w26_98
  have w27_9c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K27.w32 (by decide) (by decide)).trans w26_9c
  have w27_a0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K27.w32 (by decide) (by decide)).trans w26_a0
  have w27_a4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K27.w32 (by decide) (by decide)).trans w26_a4
  have w27_150 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K27.w32 (by decide) (by decide)).trans w26_150
  have w27_154 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K27.w32 (by decide) (by decide)).trans w26_154
  have w27_158 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = (cur) + BitVec.ofNat 32 (tl10.header + tl10.len) := (K27.w32 (by decide) (by decide)).trans w26_158
  have w27_15c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = (rem) - BitVec.ofNat 32 (tl10.header + tl10.len) := (K27.w32 (by decide) (by decide)).trans w26_15c
  have w27_400 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10.header := (K27.w32 (by decide) (by decide)).trans w26_400
  have w27_408 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = ((cur) + BitVec.ofNat 32 tl10.header) + BitVec.ofNat 32 (to21.header + to21.len) := (K27.w32 (by decide) (by decide)).trans w26_408
  have w27_40c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (BitVec.ofNat 32 tl10.len) - BitVec.ofNat 32 (to21.header + to21.len) := (K27.w32 (by decide) (by decide)).trans w26_40c
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op21 := (K27.w32 (by decide) (by decide)).trans w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol21 := (K27.w32 (by decide) (by decide)).trans w26_424
  have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cur) + BitVec.ofNat 32 tl10.header := (K27.w32 (by decide) (by decide)).trans w26_428
  have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl10.len := (K27.w32 (by decide) (by decide)).trans w26_42c
  have b27_404 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl10.len).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_404
  have b27_405 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl10.len).extractLsb' 8 8 := (K27.b8 (by decide) (by decide)).trans b26_405
  have b27_406 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl10.len).extractLsb' 16 8 := (K27.b8 (by decide) (by decide)).trans b26_406
  have b27_407 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl10.len).extractLsb' 24 8 := (K27.b8 (by decide) (by decide)).trans b26_407
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol21 := by rw [W27, g26_11]
  clear b26_407 b26_406 b26_405 b26_404 w26_42c w26_428 w26_424 w26_420 w26_40c w26_408 w26_400 w26_15c w26_158 w26_154 w26_150 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_44 w26_40 w26_3c w26_30 w26_2c g26_11 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  exact .inr ⟨hz_5, tl10, hr10, op21, ol21, hr21, to21, ht21, n27, t27, s27, E27, V27, fR27, g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_11, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_25, g27_27, w27_2c, w27_30, w27_3c, w27_40, w27_44, w27_48, w27_4c, w27_50, w27_54, w27_58, w27_5c, w27_60, w27_64, w27_68, w27_6c, w27_70, w27_74, w27_78, w27_7c, w27_80, w27_84, w27_88, w27_8c, w27_90, w27_94, w27_98, w27_9c, w27_a0, w27_a4, w27_150, w27_154, w27_158, w27_15c, w27_400, w27_408, w27_40c, keep_kk27.mono (by decide)⟩

end C3.RV32.Sv
