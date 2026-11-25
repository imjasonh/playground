import C3BootProofs.Proofs.SvData

/-!
# `sigstore::verify`: an `ExtKeyUsage` OID

One pass of the `ExtKeyUsage` loop, from 0x5DC back to 0x5DC: the next entry must be an OID, and the flag in `s10` gains whether it is `codeSigning`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svDeku25e4 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x380]
theorem svDeku25e4_end : blockEnd sigstoreVerifyCode 0x5E4 svDeku25e4 = some 0x5EA := by
  simp only [svDeku25e4]
  rw [blockEnd, sv_at_5e4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_5e8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDeku25fe : List BInstr :=
  [.aluImm .add a3 x0 0x8, .lui a2 0x3FCC4000, .aluImm .add a2 a2 0x710]
theorem svDeku25fe_end : blockEnd sigstoreVerifyCode 0x5FE svDeku25fe = some 0x608 := by
  simp only [svDeku25fe]
  rw [blockEnd, sv_at_5fe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_600]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_604]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDeku2610 : List BInstr :=
  [.alu .or (26 : Fin 32) (26 : Fin 32) a0]
theorem svDeku2610_end : blockEnd sigstoreVerifyCode 0x610 svDeku2610 = some 0x614 := by
  simp only [svDeku2610]
  rw [blockEnd, sv_at_610]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_deku2 {B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c cp cl rest found : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x5DC (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
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
    (w0_15c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest)
    (w0_388 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = cp)
    (w0_38c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = cl)
    (g0_26 : reg n0 (26 : Fin 32) = found)
    (c_in : SvIn B cp cl.toNat)
    (hcl : cl ≠ 0)
    (SD0 : SvData M0) :
    (¬ (∃ op4 ol4, derContent (cp) (derOid (memBytes M0 (cp) (cl).toNat)) = .ok (op4, ol4) ∧ ∃ to4, derOid (memBytes M0 (cp) (cl).toNat) = .ok to4 ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ op4 ol4, derContent (cp) (derOid (memBytes M0 (cp) (cl).toNat)) = .ok (op4, ol4) ∧
    ∃ to4, derOid (memBytes M0 (cp) (cl).toNat) = .ok to4 ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x5DC (reg n') ∧
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
        reg n' (26 : Fin 32) = (found) ||| (if memBytes M0 op4 ol4.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x8)) 8 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) ∧
        reg n' (27 : Fin 32) = tbl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (cp) + BitVec.ofNat 32 (to4.header + to4.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (cl) - BitVec.ofNat 32 (to4.header + to4.len) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x8), (0x388, 0x8)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x5DC: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_5dc (off' := 0x5E0) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x38C = B + 0x21A0 + BitVec.ofNat 32 0x38C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0x5E0 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_9 : reg n1 (9 : Fin 32) = tbp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, upd_ne (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = dg := by rw [u1.regs, upd_ne (by decide) (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = rootp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = ll := by rw [u1.regs, upd_ne (by decide) (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = sgp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = kp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = sgl := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = found := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = tbl := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_10 : reg n1 a0 = cl := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x38C = B + 0x21A0 + BitVec.ofNat 32 0x38C by sv_addr, w0_38c]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m1]; exact w0_2c
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m1]; exact w0_30
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
  have w1_388 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = cp := by rw [m1]; exact w0_388
  have w1_38c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = cl := by rw [m1]; exact w0_38c
  -- 0x5E0: branch, not taken
  obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.self 0x5E4 sv_at_5e0
    (by decide) (by rw [g1_10, s1.zero]; exact br_beq_f hcl)
  have s2 : St n2.mem SV n2 0x5E4 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, g1_4]
  have g2_9 : reg n2 (9 : Fin 32) = tbp := by rw [u2.regs, g1_9]
  have g2_10 : reg n2 a0 = cl := by rw [u2.regs, g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [u2.regs, g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [u2.regs, g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [u2.regs, g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = sgp := by rw [u2.regs, g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = kp := by rw [u2.regs, g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = sgl := by rw [u2.regs, g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = found := by rw [u2.regs, g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = tbl := by rw [u2.regs, g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m2]; exact w1_2c
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m2]; exact w1_30
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
  have w2_388 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = cp := by rw [m2]; exact w1_388
  have w2_38c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = cl := by rw [m2]; exact w1_38c
  clear w1_38c w1_388 w1_15c w1_158 w1_154 w1_150 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_30 w1_2c g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x5E4
  obtain ⟨n3, c3, u3⟩ := s2.block svDeku25e4 E2.self svDeku25e4_end
    ⟨trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0x5EA (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock svDeku25e4 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
  have g3_9 : reg n3 (9 : Fin 32) = tbp := by
    rw [rb3, runBlock_reg _ _ _ (9 : Fin 32) s2.zero (by decide), g2_9]
  have g3_18 : reg n3 (18 : Fin 32) = out := by
    rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = dg := by
    rw [rb3, runBlock_reg _ _ _ (20 : Fin 32) s2.zero (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = rootp := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = ll := by
    rw [rb3, runBlock_reg _ _ _ (22 : Fin 32) s2.zero (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = sgp := by
    rw [rb3, runBlock_reg _ _ _ (23 : Fin 32) s2.zero (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = kp := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = sgl := by
    rw [rb3, runBlock_reg _ _ _ (25 : Fin 32) s2.zero (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = found := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = tbl := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svDeku25e4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_9, g2_10, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_11 : reg n3 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svDeku25e4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_9, g2_10, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m3]; exact w2_2c
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m3]; exact w2_30
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
  have w3_388 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = cp := by rw [m3]; exact w2_388
  have w3_38c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = cl := by rw [m3]; exact w2_38c
  clear w2_38c w2_388 w2_15c w2_158 w2_154 w2_150 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_74 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_30 w2_2c g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_9 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x5EA: sv_oidF
  obtain ⟨n4, c4, s4, sp4, rk4, K4, A4, Ok4, Er4, fr4⟩ := sv_oidF (oc := 0x420) (dc := 0x380)
    F E3 s3 sv_at_5ea sv_at_5ee (by decide) (by decide) g3_2 g3_10 g3_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w3_388 w3_38c c_in
  have t4 : Steps n0 n4 := t3.trans c4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keepL K4 (by decide)
  rw [sv_mb fR3 c_in] at A4 Ok4 Er4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rk4 sp (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk4 (3 : Fin 32) (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk4 (4 : Fin 32) (by decide) (by decide), g3_4]
  have g4_9 : reg n4 (9 : Fin 32) = tbp := by rw [rk4 (9 : Fin 32) (by decide) (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rk4 (18 : Fin 32) (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rk4 (19 : Fin 32) (by decide) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [rk4 (20 : Fin 32) (by decide) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [rk4 (21 : Fin 32) (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [rk4 (22 : Fin 32) (by decide) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = sgp := by rw [rk4 (23 : Fin 32) (by decide) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = kp := by rw [rk4 (24 : Fin 32) (by decide) (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = sgl := by rw [rk4 (25 : Fin 32) (by decide) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = found := by rw [rk4 (26 : Fin 32) (by decide) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = tbl := by rw [rk4 (27 : Fin 32) (by decide) (by decide), g3_27]
  obtain ⟨r4, hr4⟩ : ∃ r, derContent (cp) (derOid (memBytes M0 (cp) (cl).toNat)) = r := ⟨_, rfl⟩
  rcases r4 with er4 | ⟨op4, ol4⟩
  · obtain ⟨z4, -⟩ := Er4 er4 hr4
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x8), (0x388, 0x8)] := keep_kk3.trans K4
    clear keep_kk3
    have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K4.w32 (by decide) (by decide)).trans w3_2c
    have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K4.w32 (by decide) (by decide)).trans w3_30
    have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K4.w32 (by decide) (by decide)).trans w3_54
    have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K4.w32 (by decide) (by decide)).trans w3_58
    have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K4.w32 (by decide) (by decide)).trans w3_5c
    have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K4.w32 (by decide) (by decide)).trans w3_60
    have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K4.w32 (by decide) (by decide)).trans w3_64
    have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K4.w32 (by decide) (by decide)).trans w3_68
    have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K4.w32 (by decide) (by decide)).trans w3_6c
    have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K4.w32 (by decide) (by decide)).trans w3_70
    have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K4.w32 (by decide) (by decide)).trans w3_74
    have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K4.w32 (by decide) (by decide)).trans w3_78
    have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K4.w32 (by decide) (by decide)).trans w3_7c
    have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K4.w32 (by decide) (by decide)).trans w3_80
    have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K4.w32 (by decide) (by decide)).trans w3_84
    have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K4.w32 (by decide) (by decide)).trans w3_88
    have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K4.w32 (by decide) (by decide)).trans w3_8c
    have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K4.w32 (by decide) (by decide)).trans w3_90
    have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K4.w32 (by decide) (by decide)).trans w3_94
    have w4_98 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K4.w32 (by decide) (by decide)).trans w3_98
    have w4_9c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K4.w32 (by decide) (by decide)).trans w3_9c
    have w4_a0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K4.w32 (by decide) (by decide)).trans w3_a0
    have w4_a4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K4.w32 (by decide) (by decide)).trans w3_a4
    have w4_150 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K4.w32 (by decide) (by decide)).trans w3_150
    have w4_154 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K4.w32 (by decide) (by decide)).trans w3_154
    have w4_158 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K4.w32 (by decide) (by decide)).trans w3_158
    have w4_15c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K4.w32 (by decide) (by decide)).trans w3_15c
    have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z4
    clear w3_38c w3_388 w3_15c w3_158 w3_154 w3_150 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_30 w3_2c g3_11 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
    -- 0x5F2: lw
    obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_5f2 (off' := 0x5F6) (by decide)
      (by rw [g4_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s5 : St n5.mem SV n5 0x5F6 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
    have g5_9 : reg n5 (9 : Fin 32) = tbp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_9]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
    have g5_20 : reg n5 (20 : Fin 32) = dg := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
    have g5_21 : reg n5 (21 : Fin 32) = rootp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = ll := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
    have g5_23 : reg n5 (23 : Fin 32) = sgp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
    have g5_24 : reg n5 (24 : Fin 32) = kp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
    have g5_25 : reg n5 (25 : Fin 32) = sgl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = found := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = tbl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
    have g5_10 : reg n5 a0 = 0 := by
      rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g4_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w4_420]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x8), (0x388, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m5]; exact w4_2c
    have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m5]; exact w4_30
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
    have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m5]; exact w4_420
    clear w4_420 w4_15c w4_158 w4_154 w4_150 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_30 w4_2c z4
    -- 0x5F6: branch, taken
    obtain ⟨n6, d6, u6⟩ := s5.taken E5.self 0x7E8 sv_at_5f6
      (by decide) (by rw [g5_10, s5.zero]; rfl)
    have s6 : St n6.mem SV n6 0x7E8 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
    have t6 : Steps n0 n6 := t5.trans (.single d6)
    have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
    have E6 : SvCode n6.mem := E5.fr F fr6
    have V6 : SvSaves B n6.mem v := V5.same m6
    have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
    have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
    have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
    have g6_9 : reg n6 (9 : Fin 32) = tbp := by rw [u6.regs, g5_9]
    have g6_10 : reg n6 a0 = 0 := by rw [u6.regs, g5_10]
    have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
    have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [u6.regs, g5_20]
    have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [u6.regs, g5_21]
    have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [u6.regs, g5_22]
    have g6_23 : reg n6 (23 : Fin 32) = sgp := by rw [u6.regs, g5_23]
    have g6_24 : reg n6 (24 : Fin 32) = kp := by rw [u6.regs, g5_24]
    have g6_25 : reg n6 (25 : Fin 32) = sgl := by rw [u6.regs, g5_25]
    have g6_26 : reg n6 (26 : Fin 32) = found := by rw [u6.regs, g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = tbl := by rw [u6.regs, g5_27]
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x8), (0x388, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m6]; exact w5_2c
    have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m6]; exact w5_30
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
    have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m6]; exact w5_420
    clear w5_420 w5_15c w5_158 w5_154 w5_150 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_30 w5_2c g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    -- 0x7E8: lbu
    obtain ⟨n7, d7, u7⟩ := s6.lbu E6.self sv_at_7e8 (off' := 0x7EC) (by decide)
    have s7 : St n7.mem SV n7 0x7EC (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
    have g7_9 : reg n7 (9 : Fin 32) = tbp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_9]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = dg := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = rootp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = ll := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = sgp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = kp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = sgl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = found := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = tbl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x8), (0x388, 0x8)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m7]; exact w6_2c
    have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m7]; exact w6_30
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
    have w7_15c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m7]; exact w6_15c
    have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m7]; exact w6_420
    clear w6_420 w6_15c w6_158 w6_154 w6_150 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_30 w6_2c g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
    -- 0x7EC: sw
    obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_7ec (off' := 0x7EE) (c := 0x50)
      (by decide) (by rw [g7_2]; sv_addr) (by decide) (by decide)
    have t8 : Steps n0 n8 := t7.trans d8
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
    have g8_9 : reg n8 (9 : Fin 32) = tbp := by rw [rg8 (9 : Fin 32), g7_9]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [rg8 (20 : Fin 32), g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [rg8 (21 : Fin 32), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [rg8 (22 : Fin 32), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = sgp := by rw [rg8 (23 : Fin 32), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = kp := by rw [rg8 (24 : Fin 32), g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = sgl := by rw [rg8 (25 : Fin 32), g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = found := by rw [rg8 (26 : Fin 32), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = tbl := by rw [rg8 (27 : Fin 32), g7_27]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x8), (0x388, 0x8), (0x50, 0x4)] := keep_kk7.trans K8.toL
    clear keep_kk7
    have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K8.w32 (by decide) (by decide)).trans w7_2c
    have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K8.w32 (by decide) (by decide)).trans w7_30
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
    have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K8.w32 (by decide) (by decide)).trans w7_420
    clear w7_420 w7_15c w7_158 w7_154 w7_150 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_30 w7_2c g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
    -- 0x7EE: lw
    obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_7ee (off' := 0x7F0) (by decide)
      (by rw [g8_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s9 : St n9.mem SV n9 0x7F0 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
    have g9_9 : reg n9 (9 : Fin 32) = tbp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [u9.regs, upd_ne (by decide) (by decide), g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = sgp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = kp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = sgl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = found := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = tbl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x8), (0x388, 0x8), (0x50, 0x4)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m9]; exact w8_2c
    have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m9]; exact w8_30
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
    have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m9]; exact w8_420
    clear w8_420 w8_15c w8_158 w8_154 w8_150 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_30 w8_2c g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
    -- 0x7F0: j
    obtain ⟨n10, d10, u10⟩ := s9.jump E9.self sv_at_7f0 (off' := 0x942) (by decide)
      (by rw [s9.pc]; decide)
    have s10 : St n10.mem SV n10 0x942 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
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
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = dg := by rw [u10.regs, g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = rootp := by rw [u10.regs, g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = ll := by rw [u10.regs, g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = sgp := by rw [u10.regs, g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = kp := by rw [u10.regs, g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = sgl := by rw [u10.regs, g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = found := by rw [u10.regs, g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = tbl := by rw [u10.regs, g9_27]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x8), (0x388, 0x8), (0x50, 0x4)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m10]; exact w9_2c
    have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m10]; exact w9_30
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
    have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m10]; exact w9_420
    clear w9_420 w9_15c w9_158 w9_154 w9_150 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_30 w9_2c g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
    -- 0x942: sw
    obtain ⟨n11, d11, s11, fr11, K11, W11, rg11⟩ := sv_sw F E10 s10 sv_at_942 (off' := 0x944) (c := 0x44)
      (by decide) (by rw [g10_2]; sv_addr) (by decide) (by decide)
    have t11 : Steps n0 n11 := t10.trans d11
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.keep K11 (by decide)
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rg11 sp, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg11 (3 : Fin 32), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg11 (4 : Fin 32), g10_4]
    have g11_9 : reg n11 (9 : Fin 32) = tbp := by rw [rg11 (9 : Fin 32), g10_9]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rg11 (18 : Fin 32), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rg11 (19 : Fin 32), g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [rg11 (20 : Fin 32), g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [rg11 (21 : Fin 32), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [rg11 (22 : Fin 32), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = sgp := by rw [rg11 (23 : Fin 32), g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = kp := by rw [rg11 (24 : Fin 32), g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = sgl := by rw [rg11 (25 : Fin 32), g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = found := by rw [rg11 (26 : Fin 32), g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = tbl := by rw [rg11 (27 : Fin 32), g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x8), (0x388, 0x8), (0x50, 0x4), (0x44, 0x4)] := keep_kk10.trans K11.toL
    clear keep_kk10
    have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K11.w32 (by decide) (by decide)).trans w10_2c
    have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K11.w32 (by decide) (by decide)).trans w10_30
    have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K11.w32 (by decide) (by decide)).trans w10_54
    have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K11.w32 (by decide) (by decide)).trans w10_58
    have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K11.w32 (by decide) (by decide)).trans w10_5c
    have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K11.w32 (by decide) (by decide)).trans w10_60
    have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K11.w32 (by decide) (by decide)).trans w10_64
    have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K11.w32 (by decide) (by decide)).trans w10_68
    have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K11.w32 (by decide) (by decide)).trans w10_6c
    have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K11.w32 (by decide) (by decide)).trans w10_70
    have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K11.w32 (by decide) (by decide)).trans w10_74
    have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K11.w32 (by decide) (by decide)).trans w10_78
    have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K11.w32 (by decide) (by decide)).trans w10_7c
    have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K11.w32 (by decide) (by decide)).trans w10_80
    have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K11.w32 (by decide) (by decide)).trans w10_84
    have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K11.w32 (by decide) (by decide)).trans w10_88
    have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K11.w32 (by decide) (by decide)).trans w10_8c
    have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K11.w32 (by decide) (by decide)).trans w10_90
    have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K11.w32 (by decide) (by decide)).trans w10_94
    have w11_98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K11.w32 (by decide) (by decide)).trans w10_98
    have w11_9c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K11.w32 (by decide) (by decide)).trans w10_9c
    have w11_a0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K11.w32 (by decide) (by decide)).trans w10_a0
    have w11_a4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K11.w32 (by decide) (by decide)).trans w10_a4
    have w11_150 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K11.w32 (by decide) (by decide)).trans w10_150
    have w11_154 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K11.w32 (by decide) (by decide)).trans w10_154
    have w11_158 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K11.w32 (by decide) (by decide)).trans w10_158
    have w11_15c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K11.w32 (by decide) (by decide)).trans w10_15c
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K11.w32 (by decide) (by decide)).trans w10_420
    clear w10_420 w10_15c w10_158 w10_154 w10_150 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_30 w10_2c g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x944: lw
    obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g11_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s12 : St n12.mem SV n12 0x946 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
    have g12_9 : reg n12 (9 : Fin 32) = tbp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = dg := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = rootp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = ll := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = sgp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = kp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = sgl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = found := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = tbl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x8), (0x388, 0x8), (0x50, 0x4), (0x44, 0x4)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m12]; exact w11_2c
    have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m12]; exact w11_30
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
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m12]; exact w11_420
    clear w11_420 w11_15c w11_158 w11_154 w11_150 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_30 w11_2c g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 rg11 W11 K11 fr11 s11 d11
    -- 0x946: j
    obtain ⟨n13, d13, u13⟩ := s12.jump E12.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s12.pc]; decide)
    have s13 : St n13.mem SV n13 0x7A4 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
    have t13 : Steps n0 n13 := t12.trans (.single d13)
    have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
    have E13 : SvCode n13.mem := E12.fr F fr13
    have V13 : SvSaves B n13.mem v := V12.same m13
    have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
    have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
    have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
    have g13_9 : reg n13 (9 : Fin 32) = tbp := by rw [u13.regs, g12_9]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = dg := by rw [u13.regs, g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = rootp := by rw [u13.regs, g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = ll := by rw [u13.regs, g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = sgp := by rw [u13.regs, g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = kp := by rw [u13.regs, g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = sgl := by rw [u13.regs, g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = found := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = tbl := by rw [u13.regs, g12_27]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x8), (0x388, 0x8), (0x50, 0x4), (0x44, 0x4)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m13]; exact w12_2c
    have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m13]; exact w12_30
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
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m13]; exact w12_420
    clear w12_420 w12_15c w12_158 w12_154 w12_150 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_30 w12_2c g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    exact .inl ⟨(fun ⟨op4', ol4', h0', _⟩ => by rw [hr4] at h0'; cases h0'), sv_fail F E13 s13 t13 (fun x hx => (fR13 x hx).trans (fM x hx).symm) V13 hret g13_2 g13_18 hO g13_3 g13_4⟩
  obtain ⟨to4, ht4, -, -⟩ := oid_ok_content hr4
  obtain ⟨p0_4, p4_4⟩ := Ok4 op4 ol4 hr4
  obtain ⟨d8_4, d12_4⟩ := A4 to4 (derOid_ok_elem ht4)
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x8), (0x388, 0x8)] := keep_kk3.trans K4
  clear keep_kk3
  have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K4.w32 (by decide) (by decide)).trans w3_2c
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K4.w32 (by decide) (by decide)).trans w3_30
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K4.w32 (by decide) (by decide)).trans w3_54
  have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K4.w32 (by decide) (by decide)).trans w3_58
  have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K4.w32 (by decide) (by decide)).trans w3_5c
  have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K4.w32 (by decide) (by decide)).trans w3_60
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K4.w32 (by decide) (by decide)).trans w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K4.w32 (by decide) (by decide)).trans w3_68
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K4.w32 (by decide) (by decide)).trans w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K4.w32 (by decide) (by decide)).trans w3_70
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K4.w32 (by decide) (by decide)).trans w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K4.w32 (by decide) (by decide)).trans w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K4.w32 (by decide) (by decide)).trans w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K4.w32 (by decide) (by decide)).trans w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K4.w32 (by decide) (by decide)).trans w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K4.w32 (by decide) (by decide)).trans w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K4.w32 (by decide) (by decide)).trans w3_8c
  have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K4.w32 (by decide) (by decide)).trans w3_90
  have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K4.w32 (by decide) (by decide)).trans w3_94
  have w4_98 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K4.w32 (by decide) (by decide)).trans w3_98
  have w4_9c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K4.w32 (by decide) (by decide)).trans w3_9c
  have w4_a0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K4.w32 (by decide) (by decide)).trans w3_a0
  have w4_a4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K4.w32 (by decide) (by decide)).trans w3_a4
  have w4_150 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K4.w32 (by decide) (by decide)).trans w3_150
  have w4_154 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K4.w32 (by decide) (by decide)).trans w3_154
  have w4_158 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K4.w32 (by decide) (by decide)).trans w3_158
  have w4_15c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K4.w32 (by decide) (by decide)).trans w3_15c
  have w4_388 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (cp) + BitVec.ofNat 32 (to4.header + to4.len) := d8_4
  have w4_38c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (cl) - BitVec.ofNat 32 (to4.header + to4.len) := d12_4
  have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op4 := p0_4
  have w4_424 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol4 := p4_4
  clear w3_38c w3_388 w3_15c w3_158 w3_154 w3_150 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_30 w3_2c g3_11 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  -- 0x5F2: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_5f2 (off' := 0x5F6) (by decide)
    (by rw [g4_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0x5F6 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_9 : reg n5 (9 : Fin 32) = tbp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = dg := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = rootp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = ll := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = sgp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = kp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = sgl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = found := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = tbl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
  have g5_10 : reg n5 a0 = op4 := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w4_420]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x8), (0x388, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m5]; exact w4_2c
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m5]; exact w4_30
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
  have w5_388 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (cp) + BitVec.ofNat 32 (to4.header + to4.len) := by rw [m5]; exact w4_388
  have w5_38c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (cl) - BitVec.ofNat 32 (to4.header + to4.len) := by rw [m5]; exact w4_38c
  have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op4 := by rw [m5]; exact w4_420
  have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol4 := by rw [m5]; exact w4_424
  clear w4_424 w4_420 w4_38c w4_388 w4_15c w4_158 w4_154 w4_150 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_30 w4_2c d12_4 d8_4 p4_4 p0_4 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 Er4 Ok4 A4 K4 rk4 sp4 s4 c4
  -- 0x5F6: branch, not taken
  obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.self 0x5FA sv_at_5f6
    (by decide) (by rw [g5_10, s5.zero]; exact br_beq_f ((c_in.oidIn hr4).pos_ne))
  have s6 : St n6.mem SV n6 0x5FA (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = tbp := by rw [u6.regs, g5_9]
  have g6_10 : reg n6 a0 = op4 := by rw [u6.regs, g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [u6.regs, g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [u6.regs, g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [u6.regs, g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = sgp := by rw [u6.regs, g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = kp := by rw [u6.regs, g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = sgl := by rw [u6.regs, g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = found := by rw [u6.regs, g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = tbl := by rw [u6.regs, g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x8), (0x388, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m6]; exact w5_2c
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m6]; exact w5_30
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
  have w6_388 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (cp) + BitVec.ofNat 32 (to4.header + to4.len) := by rw [m6]; exact w5_388
  have w6_38c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (cl) - BitVec.ofNat 32 (to4.header + to4.len) := by rw [m6]; exact w5_38c
  have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op4 := by rw [m6]; exact w5_420
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol4 := by rw [m6]; exact w5_424
  clear w5_424 w5_420 w5_38c w5_388 w5_15c w5_158 w5_154 w5_150 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_30 w5_2c g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x5FA: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_5fa (off' := 0x5FE) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0x5FE (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_9 : reg n7 (9 : Fin 32) = tbp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_9]
  have g7_10 : reg n7 a0 = op4 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_10]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = dg := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = rootp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = ll := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = sgp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = kp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = sgl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = found := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = tbl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
  have g7_11 : reg n7 a1 = ol4 := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w6_424]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x8), (0x388, 0x8)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m7]; exact w6_2c
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m7]; exact w6_30
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
  have w7_15c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m7]; exact w6_15c
  have w7_388 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (cp) + BitVec.ofNat 32 (to4.header + to4.len) := by rw [m7]; exact w6_388
  have w7_38c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (cl) - BitVec.ofNat 32 (to4.header + to4.len) := by rw [m7]; exact w6_38c
  have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op4 := by rw [m7]; exact w6_420
  have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol4 := by rw [m7]; exact w6_424
  clear w6_424 w6_420 w6_38c w6_388 w6_15c w6_158 w6_154 w6_150 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_30 w6_2c g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x5FE
  obtain ⟨n8, c8, u8⟩ := s7.block svDeku25fe E7.self svDeku25fe_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x608 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svDeku25fe (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_9 : reg n8 (9 : Fin 32) = tbp := by
    rw [rb8, runBlock_reg _ _ _ (9 : Fin 32) s7.zero (by decide), g7_9]
  have g8_10 : reg n8 a0 = op4 := by
    rw [rb8, runBlock_reg _ _ _ a0 s7.zero (by decide), g7_10]
  have g8_11 : reg n8 a1 = ol4 := by
    rw [rb8, runBlock_reg _ _ _ a1 s7.zero (by decide), g7_11]
  have g8_18 : reg n8 (18 : Fin 32) = out := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = dg := by
    rw [rb8, runBlock_reg _ _ _ (20 : Fin 32) s7.zero (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = rootp := by
    rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = ll := by
    rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = sgp := by
    rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = kp := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = sgl := by
    rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = found := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = tbl := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_12 : reg n8 a2 = BitVec.ofNat 32 (img% svConstAddress + 0x8) := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svDeku25fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_9, g7_10, g7_11, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_13 : reg n8 a3 = BitVec.ofNat 32 0x8 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svDeku25fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_9, g7_10, g7_11, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x8), (0x388, 0x8)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m8]; exact w7_2c
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m8]; exact w7_30
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
  have w8_15c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m8]; exact w7_15c
  have w8_388 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (cp) + BitVec.ofNat 32 (to4.header + to4.len) := by rw [m8]; exact w7_388
  have w8_38c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (cl) - BitVec.ofNat 32 (to4.header + to4.len) := by rw [m8]; exact w7_38c
  have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op4 := by rw [m8]; exact w7_420
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol4 := by rw [m8]; exact w7_424
  clear w7_424 w7_420 w7_38c w7_388 w7_15c w7_158 w7_154 w7_150 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_30 w7_2c g7_11 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x608: sv_seqEqF
  obtain ⟨n9, c9, s9, rk9, a0_9, K9, fr9⟩ := sv_seqEqF (pl := ol4.toNat) (ql := 8)
    F E8 s8 sv_at_608 sv_at_60c (by decide) (by decide) g8_2
    g8_10 (by rw [g8_11, ofNat_toNat_self]) g8_12 g8_13 (.inl (c_in.oidIn hr4)) (.inr ⟨by decide, by decide⟩)
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keepL K9 (by decide)
  rw [sv_mbRo FW fR8 (.inl (c_in.oidIn hr4)), sv_mbRo FW fR8 (.inr ⟨by decide, by decide⟩)] at a0_9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rk9 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk9 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk9 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_4]
  have g9_9 : reg n9 (9 : Fin 32) = tbp := by rw [rk9 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rk9 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rk9 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [rk9 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [rk9 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [rk9 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = sgp := by rw [rk9 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = kp := by rw [rk9 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = sgl := by rw [rk9 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = found := by rw [rk9 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = tbl := by rw [rk9 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x8), (0x388, 0x8)] := keep_kk8.trans K9
  clear keep_kk8
  have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K9.w32 (by decide) (by decide)).trans w8_2c
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K9.w32 (by decide) (by decide)).trans w8_30
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
  have w9_15c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K9.w32 (by decide) (by decide)).trans w8_15c
  have w9_388 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (cp) + BitVec.ofNat 32 (to4.header + to4.len) := (K9.w32 (by decide) (by decide)).trans w8_388
  have w9_38c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (cl) - BitVec.ofNat 32 (to4.header + to4.len) := (K9.w32 (by decide) (by decide)).trans w8_38c
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op4 := (K9.w32 (by decide) (by decide)).trans w8_420
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol4 := (K9.w32 (by decide) (by decide)).trans w8_424
  clear w8_424 w8_420 w8_38c w8_388 w8_15c w8_158 w8_154 w8_150 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_30 w8_2c g8_13 g8_12 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_11 g8_10 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  have g9_10 : reg n9 a0 = if memBytes M0 op4 ol4.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x8)) 8 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := a0_9
  -- 0x610
  obtain ⟨n10, c10, u10⟩ := s9.block svDeku2610 E9.self svDeku2610_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x614 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svDeku2610 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans c10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by
    rw [rb10, runBlock_reg _ _ _ sp s9.zero (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (3 : Fin 32) s9.zero (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (4 : Fin 32) s9.zero (by decide), g9_4]
  have g10_9 : reg n10 (9 : Fin 32) = tbp := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_10 : reg n10 a0 = if memBytes M0 op4 ol4.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x8)) 8 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by
    rw [rb10, runBlock_reg _ _ _ a0 s9.zero (by decide), g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = dg := by
    rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = rootp := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = ll := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = sgp := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = kp := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = sgl := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_27 : reg n10 (27 : Fin 32) = tbl := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_26 : reg n10 (26 : Fin 32) = (found) ||| (if memBytes M0 op4 ol4.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x8)) 8 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) := by
    rw [rb10, ← g9_26, ← g9_10]; rfl
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x8), (0x388, 0x8)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m10]; exact w9_2c
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m10]; exact w9_30
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
  have w10_388 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (cp) + BitVec.ofNat 32 (to4.header + to4.len) := by rw [m10]; exact w9_388
  have w10_38c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (cl) - BitVec.ofNat 32 (to4.header + to4.len) := by rw [m10]; exact w9_38c
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op4 := by rw [m10]; exact w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol4 := by rw [m10]; exact w9_424
  clear w9_424 w9_420 w9_38c w9_388 w9_15c w9_158 w9_154 w9_150 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_30 w9_2c g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 K9 a0_9 rk9 s9 c9
  -- 0x614: j
  obtain ⟨n11, d11, u11⟩ := s10.jump E10.self sv_at_614 (off' := 0x5DC) (by decide)
    (by rw [s10.pc]; decide)
  have s11 : St n11.mem SV n11 0x5DC (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_9 : reg n11 (9 : Fin 32) = tbp := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = if memBytes M0 op4 ol4.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x8)) 8 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by rw [u11.regs, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [u11.regs, g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [u11.regs, g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [u11.regs, g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = sgp := by rw [u11.regs, g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = kp := by rw [u11.regs, g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = sgl := by rw [u11.regs, g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = (found) ||| (if memBytes M0 op4 ol4.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x8)) 8 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) := by rw [u11.regs, g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = tbl := by rw [u11.regs, g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x8), (0x388, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m11]; exact w10_2c
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m11]; exact w10_30
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
  have w11_388 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (cp) + BitVec.ofNat 32 (to4.header + to4.len) := by rw [m11]; exact w10_388
  have w11_38c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (cl) - BitVec.ofNat 32 (to4.header + to4.len) := by rw [m11]; exact w10_38c
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op4 := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol4 := by rw [m11]; exact w10_424
  clear w10_424 w10_420 w10_38c w10_388 w10_15c w10_158 w10_154 w10_150 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_30 w10_2c g10_26 g10_27 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10 g9_10
  exact .inr ⟨op4, ol4, hr4, to4, ht4, n11, t11, s11, E11, V11, fR11, g11_2, g11_3, g11_4, g11_9, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, w11_2c, w11_30, w11_54, w11_58, w11_5c, w11_60, w11_64, w11_68, w11_6c, w11_70, w11_74, w11_78, w11_7c, w11_80, w11_84, w11_88, w11_8c, w11_90, w11_94, w11_98, w11_9c, w11_a0, w11_a4, w11_150, w11_154, w11_158, w11_15c, w11_388, w11_38c, keep_kk11.mono (by decide)⟩

end C3.RV32.Sv
