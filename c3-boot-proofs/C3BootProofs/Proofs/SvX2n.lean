import C3BootProofs.Proofs.SvData

/-!
# `sigstore::verify`: a noncritical extension's value

From the criticality test at 0x560 to the OID tests at 0x60E, for an extension whose next byte isn't 1: its value is an OCTET STRING that ends it, and its OID isn't an earlier extension's.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svX2n56a : List BInstr :=
  [.aluImm .add a1 x0 0x1]
theorem svX2n56a_end : blockEnd sigstoreVerifyCode 0x56A svX2n56a = some 0x56C := by
  simp only [svX2n56a]
  rw [blockEnd, sv_at_56a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2n58c : List BInstr :=
  [.aluImm .add (23 : Fin 32) x0 0x0]
theorem svX2n58c_end : blockEnd sigstoreVerifyCode 0x58C svX2n58c = some 0x58E := by
  simp only [svX2n58c]
  rw [blockEnd, sv_at_58c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2n58e : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x20, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x320]
theorem svX2n58e_end : blockEnd sigstoreVerifyCode 0x58E svX2n58e = some 0x598 := by
  simp only [svX2n58e]
  rw [blockEnd, sv_at_58e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_590]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_594]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_596]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2nb36 : List BInstr :=
  [.aluImm .add a0 x0 0x1]
theorem svX2nb36_end : blockEnd sigstoreVerifyCode 0xB36 svX2nb36 = some 0xB38 := by
  simp only [svX2nb36]
  rw [blockEnd, sv_at_b36]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2n5ba : List BInstr :=
  [.alu .sub a1 (22 : Fin 32) a0, .alu .add a0 x0 (24 : Fin 32), .alu .add a2 x0 (8 : Fin 32)]
theorem svX2n5ba_end : blockEnd sigstoreVerifyCode 0x5BA svX2n5ba = some 0x5C2 := by
  simp only [svX2n5ba]
  rw [blockEnd, sv_at_5ba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_5be]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_5c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2n5cc : List BInstr :=
  [.aluImm .and a0 a0 0x1]
theorem svX2n5cc_end : blockEnd sigstoreVerifyCode 0x5CC svX2n5cc = some 0x5CE := by
  simp only [svX2n5cc]
  rw [blockEnd, sv_at_5cc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svX2n5d6 : List BInstr :=
  [.aluImm .and a0 a0 0x1, .aluImm .add a1 x0 0x16]
theorem svX2n5d6_end : blockEnd sigstoreVerifyCode 0x5D6 svX2n5d6 = some 0x5DA := by
  simp only [svX2n5d6]
  rw [blockEnd, sv_at_5d6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_5d8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_x2n {B out bp x9 x21 x25 x26 f30 f34 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 op rem2 ol rest rp2 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x560 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = op)
    (g0_9 : reg n0 (9 : Fin 32) = x9)
    (g0_10 : reg n0 a0 = rem2)
    (g0_11 : reg n0 a1 = ol)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = L)
    (g0_24 : reg n0 (24 : Fin 32) = p0)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
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
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L)
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0)
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1)
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2)
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3)
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4)
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5)
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6)
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7)
    (w0_a40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8)
    (w0_a44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest)
    (w0_328 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = rp2)
    (w0_32c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = rem2)
    (in2 : SvIn B rp2 rem2.toNat)
    (oid_in : SvIn B op ol.toNat)
    (ea_in : SvIn B p0 (L.toNat - rem.toNat))
    (hle : rem.toNat ≤ L.toNat)
    (hr2 : rem2 ≠ 0)
    (hb1 : M0 rp2 ≠ BitVec.ofNat 8 1) :
    (¬ (∃ vp8 vl8, derContent (rp2) (derElement 4 (memBytes M0 (rp2) (rem2).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 (rp2) (rem2).toNat) = .ok te8 ∧ ((rem2) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op ol.toNat) = .ok false ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ vp8 vl8, derContent (rp2) (derElement 4 (memBytes M0 (rp2) (rem2).toNat)) = .ok (vp8, vl8) ∧
    ∃ te8, derElement 4 (memBytes M0 (rp2) (rem2).toNat) = .ok te8 ∧
    ((rem2) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧
    listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op ol.toNat) = .ok false ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x60E (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = op ∧
        reg n' (9 : Fin 32) = x9 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x560: branch, not taken
  obtain ⟨n1, d1, u1⟩ := s0.notTaken E0.self 0x562 sv_at_560
    (by decide) (by rw [g0_10, s0.zero]; exact br_beq_f hr2)
  have s1 : St n1.mem SV n1 0x562 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = op := by rw [u1.regs, g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = x9 := by rw [u1.regs, g0_9]
  have g1_10 : reg n1 a0 = rem2 := by rw [u1.regs, g0_10]
  have g1_11 : reg n1 a1 = ol := by rw [u1.regs, g0_11]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = L := by rw [u1.regs, g0_22]
  have g1_24 : reg n1 (24 : Fin 32) = p0 := by rw [u1.regs, g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u1.regs, g0_27]
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m1]; exact w0_30
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m1]; exact w0_34
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m1]; exact w0_40
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m1]; exact w0_48
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m1]; exact w0_4c
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
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
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m1]; exact w0_80
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m1]; exact w0_84
  have w1_88 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m1]; exact w0_88
  have w1_8c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m1]; exact w0_8c
  have w1_90 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m1]; exact w0_90
  have w1_94 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m1]; exact w0_94
  have w1_328 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = rp2 := by rw [m1]; exact w0_328
  have w1_32c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = rem2 := by rw [m1]; exact w0_32c
  have w1_a20 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m1]; exact w0_a20
  have w1_a24 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m1]; exact w0_a24
  have w1_a28 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m1]; exact w0_a28
  have w1_a2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m1]; exact w0_a2c
  have w1_a30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m1]; exact w0_a30
  have w1_a34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m1]; exact w0_a34
  have w1_a38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m1]; exact w0_a38
  have w1_a3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m1]; exact w0_a3c
  have w1_a40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m1]; exact w0_a40
  have w1_a44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m1]; exact w0_a44
  -- 0x562: lw
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_562 (off' := 0x566) (by decide)
    (by rw [g1_2, show B + 0x21A0 + 0x328 = B + 0x21A0 + BitVec.ofNat 32 0x328 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s2 : St n2.mem SV n2 0x566 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = op := by rw [u2.regs, upd_ne (by decide) (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = x9 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_9]
  have g2_11 : reg n2 a1 = ol := by rw [u2.regs, upd_ne (by decide) (by decide), g1_11]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = L := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_24 : reg n2 (24 : Fin 32) = p0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_10 : reg n2 a0 = rp2 := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_2, show B + 0x21A0 + 0x328 = B + 0x21A0 + BitVec.ofNat 32 0x328 by sv_addr, w1_328]
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m2]; exact w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m2]; exact w1_34
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m2]; exact w1_40
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m2]; exact w1_48
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m2]; exact w1_4c
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
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
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m2]; exact w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m2]; exact w1_84
  have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m2]; exact w1_88
  have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m2]; exact w1_8c
  have w2_90 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m2]; exact w1_90
  have w2_94 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m2]; exact w1_94
  have w2_328 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = rp2 := by rw [m2]; exact w1_328
  have w2_32c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = rem2 := by rw [m2]; exact w1_32c
  have w2_a20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m2]; exact w1_a20
  have w2_a24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m2]; exact w1_a24
  have w2_a28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m2]; exact w1_a28
  have w2_a2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m2]; exact w1_a2c
  have w2_a30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m2]; exact w1_a30
  have w2_a34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m2]; exact w1_a34
  have w2_a38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m2]; exact w1_a38
  have w2_a3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m2]; exact w1_a3c
  have w2_a40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m2]; exact w1_a40
  have w2_a44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m2]; exact w1_a44
  clear w1_a44 w1_a40 w1_a3c w1_a38 w1_a34 w1_a30 w1_a2c w1_a28 w1_a24 w1_a20 w1_32c w1_328 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_40 w1_34 w1_30 g1_27 g1_26 g1_25 g1_24 g1_22 g1_21 g1_19 g1_18 g1_11 g1_10 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x566: lbu from the bundle
  obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_566 (off' := 0x56A) (by decide)
  have s3 : St n3.mem SV n3 0x56A (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = op := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = x9 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_11 : reg n3 a1 = ol := by rw [u3.regs, upd_ne (by decide) (by decide), g2_11]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = L := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_24 : reg n3 (24 : Fin 32) = p0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_10 : reg n3 a0 = (M0 (rp2)).zeroExtend 32 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_10, show (rp2) + 0x0 = rp2 from BitVec.add_zero _, fR2 _ (in2.r0 (toNat_pos_of_ne hr2))]
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m3]; exact w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m3]; exact w2_34
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m3]; exact w2_40
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m3]; exact w2_48
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m3]; exact w2_4c
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
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
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m3]; exact w2_84
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m3]; exact w2_88
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m3]; exact w2_8c
  have w3_90 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m3]; exact w2_90
  have w3_94 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m3]; exact w2_94
  have w3_328 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = rp2 := by rw [m3]; exact w2_328
  have w3_32c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = rem2 := by rw [m3]; exact w2_32c
  have w3_a20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m3]; exact w2_a20
  have w3_a24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m3]; exact w2_a24
  have w3_a28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m3]; exact w2_a28
  have w3_a2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m3]; exact w2_a2c
  have w3_a30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m3]; exact w2_a30
  have w3_a34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m3]; exact w2_a34
  have w3_a38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m3]; exact w2_a38
  have w3_a3c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m3]; exact w2_a3c
  have w3_a40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m3]; exact w2_a40
  have w3_a44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m3]; exact w2_a44
  clear w2_a44 w2_a40 w2_a3c w2_a38 w2_a34 w2_a30 w2_a2c w2_a28 w2_a24 w2_a20 w2_32c w2_328 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_74 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_48 w2_40 w2_34 w2_30 g2_10 g2_27 g2_26 g2_25 g2_24 g2_22 g2_21 g2_19 g2_18 g2_11 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x56A
  obtain ⟨n4, c4, u4⟩ := s3.block svX2n56a E3.self svX2n56a_end
    ⟨trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x56C (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svX2n56a (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_8 : reg n4 (8 : Fin 32) = op := by
    rw [rb4, runBlock_reg _ _ _ (8 : Fin 32) s3.zero (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = x9 := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
  have g4_10 : reg n4 a0 = (M0 (rp2)).zeroExtend 32 := by
    rw [rb4, runBlock_reg _ _ _ a0 s3.zero (by decide), g3_10]
  have g4_18 : reg n4 (18 : Fin 32) = out := by
    rw [rb4, runBlock_reg _ _ _ (18 : Fin 32) s3.zero (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by
    rw [rb4, runBlock_reg _ _ _ (21 : Fin 32) s3.zero (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = L := by
    rw [rb4, runBlock_reg _ _ _ (22 : Fin 32) s3.zero (by decide), g3_22]
  have g4_24 : reg n4 (24 : Fin 32) = p0 := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_11 : reg n4 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svX2n56a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_11, g3_18, g3_19, g3_21, g3_22, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m4]; exact w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m4]; exact w3_34
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m4]; exact w3_40
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m4]; exact w3_48
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m4]; exact w3_4c
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m4]; exact w3_50
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
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m4]; exact w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m4]; exact w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m4]; exact w3_8c
  have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m4]; exact w3_90
  have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m4]; exact w3_94
  have w4_328 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = rp2 := by rw [m4]; exact w3_328
  have w4_32c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = rem2 := by rw [m4]; exact w3_32c
  have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m4]; exact w3_a20
  have w4_a24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m4]; exact w3_a24
  have w4_a28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m4]; exact w3_a28
  have w4_a2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m4]; exact w3_a2c
  have w4_a30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m4]; exact w3_a30
  have w4_a34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m4]; exact w3_a34
  have w4_a38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m4]; exact w3_a38
  have w4_a3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m4]; exact w3_a3c
  have w4_a40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m4]; exact w3_a40
  have w4_a44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m4]; exact w3_a44
  clear w3_a44 w3_a40 w3_a3c w3_a38 w3_a34 w3_a30 w3_a2c w3_a28 w3_a24 w3_a20 w3_32c w3_328 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_40 w3_34 w3_30 g3_10 g3_27 g3_26 g3_25 g3_24 g3_22 g3_21 g3_19 g3_18 g3_11 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x56C: branch, taken
  obtain ⟨n5, d5, u5⟩ := s4.taken E4.self 0x58C sv_at_56c
    (by decide) (by rw [g4_10, g4_11]; exact br_bne_byte_t (by decide) hb1)
  have s5 : St n5.mem SV n5 0x58C (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = op := by rw [u5.regs, g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = x9 := by rw [u5.regs, g4_9]
  have g5_10 : reg n5 a0 = (M0 (rp2)).zeroExtend 32 := by rw [u5.regs, g4_10]
  have g5_11 : reg n5 a1 = BitVec.ofNat 32 0x1 := by rw [u5.regs, g4_11]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = L := by rw [u5.regs, g4_22]
  have g5_24 : reg n5 (24 : Fin 32) = p0 := by rw [u5.regs, g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, g4_27]
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m5]; exact w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m5]; exact w4_34
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m5]; exact w4_40
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m5]; exact w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m5]; exact w4_4c
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
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
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m5]; exact w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m5]; exact w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m5]; exact w4_8c
  have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m5]; exact w4_90
  have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m5]; exact w4_94
  have w5_328 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = rp2 := by rw [m5]; exact w4_328
  have w5_32c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = rem2 := by rw [m5]; exact w4_32c
  have w5_a20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m5]; exact w4_a20
  have w5_a24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m5]; exact w4_a24
  have w5_a28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m5]; exact w4_a28
  have w5_a2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m5]; exact w4_a2c
  have w5_a30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m5]; exact w4_a30
  have w5_a34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m5]; exact w4_a34
  have w5_a38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m5]; exact w4_a38
  have w5_a3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m5]; exact w4_a3c
  have w5_a40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m5]; exact w4_a40
  have w5_a44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m5]; exact w4_a44
  clear w4_a44 w4_a40 w4_a3c w4_a38 w4_a34 w4_a30 w4_a2c w4_a28 w4_a24 w4_a20 w4_32c w4_328 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_40 w4_34 w4_30 g4_11 g4_27 g4_26 g4_25 g4_24 g4_22 g4_21 g4_19 g4_18 g4_10 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x58C
  obtain ⟨n6, c6, u6⟩ := s5.block svX2n58c E5.self svX2n58c_end
    ⟨trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x58E (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svX2n58c (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_8 : reg n6 (8 : Fin 32) = op := by
    rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = x9 := by
    rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
  have g6_10 : reg n6 a0 = (M0 (rp2)).zeroExtend 32 := by
    rw [rb6, runBlock_reg _ _ _ a0 s5.zero (by decide), g5_10]
  have g6_11 : reg n6 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb6, runBlock_reg _ _ _ a1 s5.zero (by decide), g5_11]
  have g6_18 : reg n6 (18 : Fin 32) = out := by
    rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by
    rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = L := by
    rw [rb6, runBlock_reg _ _ _ (22 : Fin 32) s5.zero (by decide), g5_22]
  have g6_24 : reg n6 (24 : Fin 32) = p0 := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_23 : reg n6 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svX2n58c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_11, g5_18, g5_19, g5_21, g5_22, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m6]; exact w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m6]; exact w5_34
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m6]; exact w5_40
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m6]; exact w5_48
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m6]; exact w5_4c
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
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
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m6]; exact w5_84
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m6]; exact w5_88
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m6]; exact w5_8c
  have w6_90 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m6]; exact w5_90
  have w6_94 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m6]; exact w5_94
  have w6_328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = rp2 := by rw [m6]; exact w5_328
  have w6_32c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = rem2 := by rw [m6]; exact w5_32c
  have w6_a20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m6]; exact w5_a20
  have w6_a24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m6]; exact w5_a24
  have w6_a28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m6]; exact w5_a28
  have w6_a2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m6]; exact w5_a2c
  have w6_a30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m6]; exact w5_a30
  have w6_a34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m6]; exact w5_a34
  have w6_a38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m6]; exact w5_a38
  have w6_a3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m6]; exact w5_a3c
  have w6_a40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m6]; exact w5_a40
  have w6_a44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m6]; exact w5_a44
  clear w5_a44 w5_a40 w5_a3c w5_a38 w5_a34 w5_a30 w5_a2c w5_a28 w5_a24 w5_a20 w5_32c w5_328 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_40 w5_34 w5_30 g5_27 g5_26 g5_25 g5_24 g5_22 g5_21 g5_19 g5_18 g5_11 g5_10 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x58E
  obtain ⟨n7, c7, u7⟩ := s6.block svX2n58e E6.self svX2n58e_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x598 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svX2n58e (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_8 : reg n7 (8 : Fin 32) = op := by
    rw [rb7, runBlock_reg _ _ _ (8 : Fin 32) s6.zero (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = x9 := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = out := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = L := by
    rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = p0 := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svX2n58e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_11, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g7_11 : reg n7 a1 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svX2n58e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_11, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m7]; exact w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m7]; exact w6_34
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m7]; exact w6_40
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m7]; exact w6_48
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m7]; exact w6_4c
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
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
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m7]; exact w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m7]; exact w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m7]; exact w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m7]; exact w6_8c
  have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m7]; exact w6_90
  have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m7]; exact w6_94
  have w7_328 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = rp2 := by rw [m7]; exact w6_328
  have w7_32c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = rem2 := by rw [m7]; exact w6_32c
  have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m7]; exact w6_a20
  have w7_a24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m7]; exact w6_a24
  have w7_a28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m7]; exact w6_a28
  have w7_a2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m7]; exact w6_a2c
  have w7_a30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m7]; exact w6_a30
  have w7_a34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m7]; exact w6_a34
  have w7_a38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m7]; exact w6_a38
  have w7_a3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m7]; exact w6_a3c
  have w7_a40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m7]; exact w6_a40
  have w7_a44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m7]; exact w6_a44
  clear w6_a44 w6_a40 w6_a3c w6_a38 w6_a34 w6_a30 w6_a2c w6_a28 w6_a24 w6_a20 w6_32c w6_328 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_40 w6_34 w6_30 g6_23 g6_27 g6_26 g6_25 g6_24 g6_22 g6_21 g6_19 g6_18 g6_11 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0x598: sv_octF
  obtain ⟨n8, c8, s8, sp8, rk8, K8, A8, Ok8, Er8, fr8⟩ := sv_octF (oc := 0x1020) (dc := 0x320)
    F E7 s7 sv_at_598 sv_at_59c (by decide) (by decide) g7_2 g7_10 g7_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w7_328 w7_32c in2
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keepL K8 (by decide)
  rw [sv_mb fR7 in2] at A8 Ok8 Er8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rk8 sp (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk8 (3 : Fin 32) (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk8 (4 : Fin 32) (by decide) (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = op := by rw [rk8 (8 : Fin 32) (by decide) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = x9 := by rw [rk8 (9 : Fin 32) (by decide) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rk8 (18 : Fin 32) (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rk8 (19 : Fin 32) (by decide) (by decide), g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [rk8 (21 : Fin 32) (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = L := by rw [rk8 (22 : Fin 32) (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rk8 (23 : Fin 32) (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = p0 := by rw [rk8 (24 : Fin 32) (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [rk8 (25 : Fin 32) (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [rk8 (26 : Fin 32) (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk8 (27 : Fin 32) (by decide) (by decide), g7_27]
  obtain ⟨r8, hr8⟩ : ∃ r, derContent (rp2) (derElement 4 (memBytes M0 (rp2) (rem2).toNat)) = r := ⟨_, rfl⟩
  rcases r8 with er8 | ⟨vp8, vl8⟩
  · obtain ⟨z8, -⟩ := Er8 er8 hr8
    have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K8.w32 (by decide) (by decide)).trans w7_30
    have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K8.w32 (by decide) (by decide)).trans w7_34
    have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K8.w32 (by decide) (by decide)).trans w7_40
    have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K8.w32 (by decide) (by decide)).trans w7_48
    have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K8.w32 (by decide) (by decide)).trans w7_4c
    have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K8.w32 (by decide) (by decide)).trans w7_50
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
    have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K8.w32 (by decide) (by decide)).trans w7_80
    have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K8.w32 (by decide) (by decide)).trans w7_84
    have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K8.w32 (by decide) (by decide)).trans w7_88
    have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K8.w32 (by decide) (by decide)).trans w7_8c
    have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K8.w32 (by decide) (by decide)).trans w7_90
    have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K8.w32 (by decide) (by decide)).trans w7_94
    have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K8.w32 (by decide) (by decide)).trans w7_a20
    have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K8.w32 (by decide) (by decide)).trans w7_a24
    have w8_a28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K8.w32 (by decide) (by decide)).trans w7_a28
    have w8_a2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K8.w32 (by decide) (by decide)).trans w7_a2c
    have w8_a30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K8.w32 (by decide) (by decide)).trans w7_a30
    have w8_a34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K8.w32 (by decide) (by decide)).trans w7_a34
    have w8_a38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K8.w32 (by decide) (by decide)).trans w7_a38
    have w8_a3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K8.w32 (by decide) (by decide)).trans w7_a3c
    have w8_a40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K8.w32 (by decide) (by decide)).trans w7_a40
    have w8_a44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K8.w32 (by decide) (by decide)).trans w7_a44
    have w8_1020 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := z8
    clear w7_a44 w7_a40 w7_a3c w7_a38 w7_a34 w7_a30 w7_a2c w7_a28 w7_a24 w7_a20 w7_32c w7_328 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_40 w7_34 w7_30 g7_11 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
    -- 0x5A0: lw
    obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_5a0 (off' := 0x5A4) (by decide)
      (by rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s9 : St n9.mem SV n9 0x5A4 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = op := by rw [u9.regs, upd_ne (by decide) (by decide), g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = x9 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = L := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = p0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
    have g9_10 : reg n9 a0 = 0 := by
      rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr, w8_1020]
    have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m9]; exact w8_30
    have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m9]; exact w8_34
    have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m9]; exact w8_40
    have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m9]; exact w8_48
    have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m9]; exact w8_4c
    have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
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
    have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m9]; exact w8_80
    have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m9]; exact w8_84
    have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m9]; exact w8_88
    have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m9]; exact w8_8c
    have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m9]; exact w8_90
    have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m9]; exact w8_94
    have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m9]; exact w8_a20
    have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m9]; exact w8_a24
    have w9_a28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m9]; exact w8_a28
    have w9_a2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m9]; exact w8_a2c
    have w9_a30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m9]; exact w8_a30
    have w9_a34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m9]; exact w8_a34
    have w9_a38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m9]; exact w8_a38
    have w9_a3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m9]; exact w8_a3c
    have w9_a40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m9]; exact w8_a40
    have w9_a44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m9]; exact w8_a44
    have w9_1020 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m9]; exact w8_1020
    clear w8_1020 w8_a44 w8_a40 w8_a3c w8_a38 w8_a34 w8_a30 w8_a2c w8_a28 w8_a24 w8_a20 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_40 w8_34 w8_30 z8
    -- 0x5A4: sw
    obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_5a4 (off' := 0x5A6) (c := 0x3C)
      (by decide) (by rw [g9_2]; sv_addr) (by decide) (by decide)
    have t10 : Steps n0 n10 := t9.trans d10
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = op := by rw [rg10 (8 : Fin 32), g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = x9 := by rw [rg10 (9 : Fin 32), g9_9]
    have g10_10 : reg n10 a0 = 0 := by rw [rg10 a0, g9_10]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rg10 (18 : Fin 32), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rg10 (19 : Fin 32), g9_19]
    have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [rg10 (21 : Fin 32), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = L := by rw [rg10 (22 : Fin 32), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg10 (23 : Fin 32), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = p0 := by rw [rg10 (24 : Fin 32), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [rg10 (25 : Fin 32), g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [rg10 (26 : Fin 32), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg10 (27 : Fin 32), g9_27]
    have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K10.w32 (by decide) (by decide)).trans w9_30
    have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K10.w32 (by decide) (by decide)).trans w9_34
    have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K10.w32 (by decide) (by decide)).trans w9_40
    have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K10.w32 (by decide) (by decide)).trans w9_48
    have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K10.w32 (by decide) (by decide)).trans w9_4c
    have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K10.w32 (by decide) (by decide)).trans w9_50
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
    have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K10.w32 (by decide) (by decide)).trans w9_80
    have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K10.w32 (by decide) (by decide)).trans w9_84
    have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K10.w32 (by decide) (by decide)).trans w9_88
    have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K10.w32 (by decide) (by decide)).trans w9_8c
    have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K10.w32 (by decide) (by decide)).trans w9_90
    have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K10.w32 (by decide) (by decide)).trans w9_94
    have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K10.w32 (by decide) (by decide)).trans w9_a20
    have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K10.w32 (by decide) (by decide)).trans w9_a24
    have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K10.w32 (by decide) (by decide)).trans w9_a28
    have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K10.w32 (by decide) (by decide)).trans w9_a2c
    have w10_a30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K10.w32 (by decide) (by decide)).trans w9_a30
    have w10_a34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K10.w32 (by decide) (by decide)).trans w9_a34
    have w10_a38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K10.w32 (by decide) (by decide)).trans w9_a38
    have w10_a3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K10.w32 (by decide) (by decide)).trans w9_a3c
    have w10_a40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K10.w32 (by decide) (by decide)).trans w9_a40
    have w10_a44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K10.w32 (by decide) (by decide)).trans w9_a44
    have w10_1020 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := (K10.w32 (by decide) (by decide)).trans w9_1020
    have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = 0 := by rw [W10, g9_10]
    clear w9_1020 w9_a44 w9_a40 w9_a3c w9_a38 w9_a34 w9_a30 w9_a2c w9_a28 w9_a24 w9_a20 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_40 w9_34 w9_30 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
    -- 0x5A6: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x9BA sv_at_5a6
      (by decide) (by rw [g10_10, s10.zero]; rfl)
    have s11 : St n11.mem SV n11 0x9BA (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = op := by rw [u11.regs, g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = x9 := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = 0 := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = L := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = p0 := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, g10_27]
    have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m11]; exact w10_30
    have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m11]; exact w10_34
    have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = 0 := by rw [m11]; exact w10_3c
    have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m11]; exact w10_40
    have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m11]; exact w10_48
    have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m11]; exact w10_4c
    have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
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
    have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m11]; exact w10_80
    have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m11]; exact w10_84
    have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m11]; exact w10_88
    have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m11]; exact w10_8c
    have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m11]; exact w10_90
    have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m11]; exact w10_94
    have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m11]; exact w10_a20
    have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m11]; exact w10_a24
    have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m11]; exact w10_a28
    have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m11]; exact w10_a2c
    have w11_a30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m11]; exact w10_a30
    have w11_a34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m11]; exact w10_a34
    have w11_a38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m11]; exact w10_a38
    have w11_a3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m11]; exact w10_a3c
    have w11_a40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m11]; exact w10_a40
    have w11_a44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m11]; exact w10_a44
    have w11_1020 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m11]; exact w10_1020
    clear w10_3c w10_1020 w10_a44 w10_a40 w10_a3c w10_a38 w10_a34 w10_a30 w10_a2c w10_a28 w10_a24 w10_a20 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_40 w10_34 w10_30 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
    -- 0x9BA: lbu
    obtain ⟨n12, d12, u12⟩ := s11.lbu E11.self sv_at_9ba (off' := 0x9BE) (by decide)
    have s12 : St n12.mem SV n12 0x9BE (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
    have g12_8 : reg n12 (8 : Fin 32) = op := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
    have g12_9 : reg n12 (9 : Fin 32) = x9 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = L := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = p0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
    have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m12]; exact w11_30
    have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m12]; exact w11_34
    have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = 0 := by rw [m12]; exact w11_3c
    have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m12]; exact w11_40
    have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m12]; exact w11_48
    have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m12]; exact w11_4c
    have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
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
    have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m12]; exact w11_80
    have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m12]; exact w11_84
    have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m12]; exact w11_88
    have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m12]; exact w11_8c
    have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m12]; exact w11_90
    have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m12]; exact w11_94
    have w12_a20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m12]; exact w11_a20
    have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m12]; exact w11_a24
    have w12_a28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m12]; exact w11_a28
    have w12_a2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m12]; exact w11_a2c
    have w12_a30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m12]; exact w11_a30
    have w12_a34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m12]; exact w11_a34
    have w12_a38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m12]; exact w11_a38
    have w12_a3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m12]; exact w11_a3c
    have w12_a40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m12]; exact w11_a40
    have w12_a44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m12]; exact w11_a44
    have w12_1020 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m12]; exact w11_1020
    clear w11_1020 w11_a44 w11_a40 w11_a3c w11_a38 w11_a34 w11_a30 w11_a2c w11_a28 w11_a24 w11_a20 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_40 w11_3c w11_34 w11_30 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    -- 0x9BE: j
    obtain ⟨n13, d13, u13⟩ := s12.jump E12.self sv_at_9be (off' := 0xB38) (by decide)
      (by rw [s12.pc]; decide)
    have s13 : St n13.mem SV n13 0xB38 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
    have t13 : Steps n0 n13 := t12.trans (.single d13)
    have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
    have E13 : SvCode n13.mem := E12.fr F fr13
    have V13 : SvSaves B n13.mem v := V12.same m13
    have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
    have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
    have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
    have g13_8 : reg n13 (8 : Fin 32) = op := by rw [u13.regs, g12_8]
    have g13_9 : reg n13 (9 : Fin 32) = x9 := by rw [u13.regs, g12_9]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = L := by rw [u13.regs, g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u13.regs, g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = p0 := by rw [u13.regs, g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u13.regs, g12_27]
    have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m13]; exact w12_30
    have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m13]; exact w12_34
    have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = 0 := by rw [m13]; exact w12_3c
    have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m13]; exact w12_40
    have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m13]; exact w12_48
    have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m13]; exact w12_4c
    have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
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
    have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m13]; exact w12_80
    have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m13]; exact w12_84
    have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m13]; exact w12_88
    have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m13]; exact w12_8c
    have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m13]; exact w12_90
    have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m13]; exact w12_94
    have w13_a20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m13]; exact w12_a20
    have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m13]; exact w12_a24
    have w13_a28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m13]; exact w12_a28
    have w13_a2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m13]; exact w12_a2c
    have w13_a30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m13]; exact w12_a30
    have w13_a34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m13]; exact w12_a34
    have w13_a38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m13]; exact w12_a38
    have w13_a3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m13]; exact w12_a3c
    have w13_a40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m13]; exact w12_a40
    have w13_a44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m13]; exact w12_a44
    have w13_1020 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m13]; exact w12_1020
    clear w12_1020 w12_a44 w12_a40 w12_a3c w12_a38 w12_a34 w12_a30 w12_a2c w12_a28 w12_a24 w12_a20 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_40 w12_3c w12_34 w12_30 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    -- 0xB38: sw
    obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_b38 (off' := 0xB3A) (c := 0x44)
      (by decide) (by rw [g13_2]; sv_addr) (by decide) (by decide)
    have t14 : Steps n0 n14 := t13.trans d14
    have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
    have E14 : SvCode n14.mem := E13.fr F fr14
    have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
    have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
    have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
    have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
    have g14_8 : reg n14 (8 : Fin 32) = op := by rw [rg14 (8 : Fin 32), g13_8]
    have g14_9 : reg n14 (9 : Fin 32) = x9 := by rw [rg14 (9 : Fin 32), g13_9]
    have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
    have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rg14 (21 : Fin 32), g13_21]
    have g14_22 : reg n14 (22 : Fin 32) = L := by rw [rg14 (22 : Fin 32), g13_22]
    have g14_23 : reg n14 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg14 (23 : Fin 32), g13_23]
    have g14_24 : reg n14 (24 : Fin 32) = p0 := by rw [rg14 (24 : Fin 32), g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [rg14 (25 : Fin 32), g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rg14 (26 : Fin 32), g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg14 (27 : Fin 32), g13_27]
    have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K14.w32 (by decide) (by decide)).trans w13_30
    have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K14.w32 (by decide) (by decide)).trans w13_34
    have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = 0 := (K14.w32 (by decide) (by decide)).trans w13_3c
    have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K14.w32 (by decide) (by decide)).trans w13_40
    have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K14.w32 (by decide) (by decide)).trans w13_48
    have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K14.w32 (by decide) (by decide)).trans w13_4c
    have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K14.w32 (by decide) (by decide)).trans w13_50
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
    have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K14.w32 (by decide) (by decide)).trans w13_80
    have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K14.w32 (by decide) (by decide)).trans w13_84
    have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K14.w32 (by decide) (by decide)).trans w13_88
    have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K14.w32 (by decide) (by decide)).trans w13_8c
    have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K14.w32 (by decide) (by decide)).trans w13_90
    have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K14.w32 (by decide) (by decide)).trans w13_94
    have w14_a20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K14.w32 (by decide) (by decide)).trans w13_a20
    have w14_a24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K14.w32 (by decide) (by decide)).trans w13_a24
    have w14_a28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K14.w32 (by decide) (by decide)).trans w13_a28
    have w14_a2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K14.w32 (by decide) (by decide)).trans w13_a2c
    have w14_a30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K14.w32 (by decide) (by decide)).trans w13_a30
    have w14_a34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K14.w32 (by decide) (by decide)).trans w13_a34
    have w14_a38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K14.w32 (by decide) (by decide)).trans w13_a38
    have w14_a3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K14.w32 (by decide) (by decide)).trans w13_a3c
    have w14_a40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K14.w32 (by decide) (by decide)).trans w13_a40
    have w14_a44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K14.w32 (by decide) (by decide)).trans w13_a44
    have w14_1020 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := (K14.w32 (by decide) (by decide)).trans w13_1020
    clear w13_1020 w13_a44 w13_a40 w13_a3c w13_a38 w13_a34 w13_a30 w13_a2c w13_a28 w13_a24 w13_a20 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_40 w13_3c w13_34 w13_30 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
    -- 0xB3A: j
    obtain ⟨n15, d15, u15⟩ := s14.jump E14.self sv_at_b3a (off' := 0xB46) (by decide)
      (by rw [s14.pc]; decide)
    have s15 : St n15.mem SV n15 0xB46 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
    have t15 : Steps n0 n15 := t14.trans (.single d15)
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.same m15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
    have g15_8 : reg n15 (8 : Fin 32) = op := by rw [u15.regs, g14_8]
    have g15_9 : reg n15 (9 : Fin 32) = x9 := by rw [u15.regs, g14_9]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
    have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = L := by rw [u15.regs, g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u15.regs, g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = p0 := by rw [u15.regs, g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u15.regs, g14_27]
    have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m15]; exact w14_30
    have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m15]; exact w14_34
    have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = 0 := by rw [m15]; exact w14_3c
    have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m15]; exact w14_40
    have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m15]; exact w14_48
    have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m15]; exact w14_4c
    have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m15]; exact w14_50
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
    have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m15]; exact w14_80
    have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m15]; exact w14_84
    have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m15]; exact w14_88
    have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m15]; exact w14_8c
    have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m15]; exact w14_90
    have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m15]; exact w14_94
    have w15_a20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m15]; exact w14_a20
    have w15_a24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m15]; exact w14_a24
    have w15_a28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m15]; exact w14_a28
    have w15_a2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m15]; exact w14_a2c
    have w15_a30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m15]; exact w14_a30
    have w15_a34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m15]; exact w14_a34
    have w15_a38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m15]; exact w14_a38
    have w15_a3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m15]; exact w14_a3c
    have w15_a40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m15]; exact w14_a40
    have w15_a44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m15]; exact w14_a44
    have w15_1020 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m15]; exact w14_1020
    clear w14_1020 w14_a44 w14_a40 w14_a3c w14_a38 w14_a34 w14_a30 w14_a2c w14_a28 w14_a24 w14_a20 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_40 w14_3c w14_34 w14_30 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
    -- 0xB46: lw
    obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_b46 (off' := 0xB48) (by decide)
      (by rw [g15_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s16 : St n16.mem SV n16 0xB48 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
    have g16_8 : reg n16 (8 : Fin 32) = op := by rw [u16.regs, upd_ne (by decide) (by decide), g15_8]
    have g16_9 : reg n16 (9 : Fin 32) = x9 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
    have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = L := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = p0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
    have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m16]; exact w15_30
    have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m16]; exact w15_34
    have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = 0 := by rw [m16]; exact w15_3c
    have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m16]; exact w15_40
    have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m16]; exact w15_48
    have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m16]; exact w15_4c
    have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
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
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m16]; exact w15_80
    have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m16]; exact w15_84
    have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m16]; exact w15_88
    have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m16]; exact w15_8c
    have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m16]; exact w15_90
    have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m16]; exact w15_94
    have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m16]; exact w15_a20
    have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m16]; exact w15_a24
    have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m16]; exact w15_a28
    have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m16]; exact w15_a2c
    have w16_a30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m16]; exact w15_a30
    have w16_a34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m16]; exact w15_a34
    have w16_a38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m16]; exact w15_a38
    have w16_a3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m16]; exact w15_a3c
    have w16_a40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m16]; exact w15_a40
    have w16_a44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m16]; exact w15_a44
    have w16_1020 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m16]; exact w15_1020
    clear w15_1020 w15_a44 w15_a40 w15_a3c w15_a38 w15_a34 w15_a30 w15_a2c w15_a28 w15_a24 w15_a20 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_40 w15_3c w15_34 w15_30 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
    -- 0xB48: j
    obtain ⟨n17, d17, u17⟩ := s16.jump E16.self sv_at_b48 (off' := 0x966) (by decide)
      (by rw [s16.pc]; decide)
    have s17 : St n17.mem SV n17 0x966 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = op := by rw [u17.regs, g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = x9 := by rw [u17.regs, g16_9]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
    have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = L := by rw [u17.regs, g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u17.regs, g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = p0 := by rw [u17.regs, g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u17.regs, g16_27]
    have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m17]; exact w16_30
    have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m17]; exact w16_34
    have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = 0 := by rw [m17]; exact w16_3c
    have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m17]; exact w16_40
    have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m17]; exact w16_48
    have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m17]; exact w16_4c
    have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
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
    have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m17]; exact w16_80
    have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m17]; exact w16_84
    have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m17]; exact w16_88
    have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m17]; exact w16_8c
    have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m17]; exact w16_90
    have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m17]; exact w16_94
    have w17_a20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m17]; exact w16_a20
    have w17_a24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m17]; exact w16_a24
    have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m17]; exact w16_a28
    have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m17]; exact w16_a2c
    have w17_a30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m17]; exact w16_a30
    have w17_a34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m17]; exact w16_a34
    have w17_a38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m17]; exact w16_a38
    have w17_a3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m17]; exact w16_a3c
    have w17_a40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m17]; exact w16_a40
    have w17_a44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m17]; exact w16_a44
    have w17_1020 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m17]; exact w16_1020
    clear w16_1020 w16_a44 w16_a40 w16_a3c w16_a38 w16_a34 w16_a30 w16_a2c w16_a28 w16_a24 w16_a20 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_40 w16_3c w16_34 w16_30 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    exact .inl ⟨(fun ⟨vp8', vl8', h0', _⟩ => by rw [hr8] at h0'; cases h0'), sv_fail F E17 s17 t17 (fun x hx => (fR17 x hx).trans (fM x hx).symm) V17 hret g17_2 g17_18 hO g17_3 g17_4⟩
  obtain ⟨te8, ht8, -, -⟩ := content_ok_elem hr8
  obtain ⟨p0_8, p4_8⟩ := Ok8 vp8 vl8 hr8
  obtain ⟨d8_8, d12_8⟩ := A8 te8 ht8
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K8.w32 (by decide) (by decide)).trans w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K8.w32 (by decide) (by decide)).trans w7_34
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K8.w32 (by decide) (by decide)).trans w7_40
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K8.w32 (by decide) (by decide)).trans w7_48
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K8.w32 (by decide) (by decide)).trans w7_4c
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K8.w32 (by decide) (by decide)).trans w7_50
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
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K8.w32 (by decide) (by decide)).trans w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K8.w32 (by decide) (by decide)).trans w7_84
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K8.w32 (by decide) (by decide)).trans w7_88
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K8.w32 (by decide) (by decide)).trans w7_8c
  have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K8.w32 (by decide) (by decide)).trans w7_90
  have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K8.w32 (by decide) (by decide)).trans w7_94
  have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K8.w32 (by decide) (by decide)).trans w7_a20
  have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K8.w32 (by decide) (by decide)).trans w7_a24
  have w8_a28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K8.w32 (by decide) (by decide)).trans w7_a28
  have w8_a2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K8.w32 (by decide) (by decide)).trans w7_a2c
  have w8_a30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K8.w32 (by decide) (by decide)).trans w7_a30
  have w8_a34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K8.w32 (by decide) (by decide)).trans w7_a34
  have w8_a38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K8.w32 (by decide) (by decide)).trans w7_a38
  have w8_a3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K8.w32 (by decide) (by decide)).trans w7_a3c
  have w8_a40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K8.w32 (by decide) (by decide)).trans w7_a40
  have w8_a44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K8.w32 (by decide) (by decide)).trans w7_a44
  have w8_328 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := d8_8
  have w8_32c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := d12_8
  have w8_1020 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := p0_8
  have w8_1024 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := p4_8
  clear w7_a44 w7_a40 w7_a3c w7_a38 w7_a34 w7_a30 w7_a2c w7_a28 w7_a24 w7_a20 w7_32c w7_328 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_40 w7_34 w7_30 g7_11 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x5A0: lw
  obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_5a0 (off' := 0x5A4) (by decide)
    (by rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s9 : St n9.mem SV n9 0x5A4 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = op := by rw [u9.regs, upd_ne (by decide) (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = x9 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = L := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = p0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
  have g9_10 : reg n9 a0 = vp8 := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr, w8_1020]
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m9]; exact w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m9]; exact w8_34
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m9]; exact w8_40
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m9]; exact w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m9]; exact w8_4c
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
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
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m9]; exact w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m9]; exact w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m9]; exact w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m9]; exact w8_8c
  have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m9]; exact w8_90
  have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m9]; exact w8_94
  have w9_328 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m9]; exact w8_328
  have w9_32c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m9]; exact w8_32c
  have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m9]; exact w8_a20
  have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m9]; exact w8_a24
  have w9_a28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m9]; exact w8_a28
  have w9_a2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m9]; exact w8_a2c
  have w9_a30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m9]; exact w8_a30
  have w9_a34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m9]; exact w8_a34
  have w9_a38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m9]; exact w8_a38
  have w9_a3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m9]; exact w8_a3c
  have w9_a40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m9]; exact w8_a40
  have w9_a44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m9]; exact w8_a44
  have w9_1020 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m9]; exact w8_1020
  have w9_1024 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m9]; exact w8_1024
  clear w8_1024 w8_1020 w8_32c w8_328 w8_a44 w8_a40 w8_a3c w8_a38 w8_a34 w8_a30 w8_a2c w8_a28 w8_a24 w8_a20 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_40 w8_34 w8_30 d12_8 d8_8 p4_8 p0_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 Er8 Ok8 A8 K8 rk8 sp8 s8 c8
  -- 0x5A4: sw
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_5a4 (off' := 0x5A6) (c := 0x3C)
    (by decide) (by rw [g9_2]; sv_addr) (by decide) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = op := by rw [rg10 (8 : Fin 32), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = x9 := by rw [rg10 (9 : Fin 32), g9_9]
  have g10_10 : reg n10 a0 = vp8 := by rw [rg10 a0, g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rg10 (18 : Fin 32), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rg10 (19 : Fin 32), g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [rg10 (21 : Fin 32), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = L := by rw [rg10 (22 : Fin 32), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg10 (23 : Fin 32), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = p0 := by rw [rg10 (24 : Fin 32), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [rg10 (25 : Fin 32), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [rg10 (26 : Fin 32), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg10 (27 : Fin 32), g9_27]
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K10.w32 (by decide) (by decide)).trans w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K10.w32 (by decide) (by decide)).trans w9_34
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K10.w32 (by decide) (by decide)).trans w9_40
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K10.w32 (by decide) (by decide)).trans w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K10.w32 (by decide) (by decide)).trans w9_4c
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K10.w32 (by decide) (by decide)).trans w9_50
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
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K10.w32 (by decide) (by decide)).trans w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K10.w32 (by decide) (by decide)).trans w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K10.w32 (by decide) (by decide)).trans w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K10.w32 (by decide) (by decide)).trans w9_8c
  have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K10.w32 (by decide) (by decide)).trans w9_90
  have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K10.w32 (by decide) (by decide)).trans w9_94
  have w10_328 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := (K10.w32 (by decide) (by decide)).trans w9_328
  have w10_32c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := (K10.w32 (by decide) (by decide)).trans w9_32c
  have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K10.w32 (by decide) (by decide)).trans w9_a20
  have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K10.w32 (by decide) (by decide)).trans w9_a24
  have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K10.w32 (by decide) (by decide)).trans w9_a28
  have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K10.w32 (by decide) (by decide)).trans w9_a2c
  have w10_a30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K10.w32 (by decide) (by decide)).trans w9_a30
  have w10_a34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K10.w32 (by decide) (by decide)).trans w9_a34
  have w10_a38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K10.w32 (by decide) (by decide)).trans w9_a38
  have w10_a3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K10.w32 (by decide) (by decide)).trans w9_a3c
  have w10_a40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K10.w32 (by decide) (by decide)).trans w9_a40
  have w10_a44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K10.w32 (by decide) (by decide)).trans w9_a44
  have w10_1020 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := (K10.w32 (by decide) (by decide)).trans w9_1020
  have w10_1024 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := (K10.w32 (by decide) (by decide)).trans w9_1024
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [W10, g9_10]
  clear w9_1024 w9_1020 w9_a44 w9_a40 w9_a3c w9_a38 w9_a34 w9_a30 w9_a2c w9_a28 w9_a24 w9_a20 w9_32c w9_328 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_40 w9_34 w9_30 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x5A6: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0x5AA sv_at_5a6
    (by decide) (by rw [g10_10, s10.zero]; exact br_beq_f ((in2.contentIn hr8).pos_ne))
  have s11 : St n11.mem SV n11 0x5AA (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = op := by rw [u11.regs, g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = x9 := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = vp8 := by rw [u11.regs, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = L := by rw [u11.regs, g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u11.regs, g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = p0 := by rw [u11.regs, g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, g10_27]
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m11]; exact w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m11]; exact w10_34
  have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m11]; exact w10_3c
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m11]; exact w10_40
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m11]; exact w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m11]; exact w10_4c
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
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
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m11]; exact w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m11]; exact w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m11]; exact w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m11]; exact w10_8c
  have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m11]; exact w10_90
  have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m11]; exact w10_94
  have w11_328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m11]; exact w10_328
  have w11_32c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m11]; exact w10_32c
  have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m11]; exact w10_a20
  have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m11]; exact w10_a24
  have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m11]; exact w10_a28
  have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m11]; exact w10_a2c
  have w11_a30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m11]; exact w10_a30
  have w11_a34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m11]; exact w10_a34
  have w11_a38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m11]; exact w10_a38
  have w11_a3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m11]; exact w10_a3c
  have w11_a40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m11]; exact w10_a40
  have w11_a44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m11]; exact w10_a44
  have w11_1020 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m11]; exact w10_1020
  have w11_1024 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m11]; exact w10_1024
  clear w10_3c w10_1024 w10_1020 w10_a44 w10_a40 w10_a3c w10_a38 w10_a34 w10_a30 w10_a2c w10_a28 w10_a24 w10_a20 w10_32c w10_328 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_40 w10_34 w10_30 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0x5AA: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_5aa (off' := 0x5AE) (by decide)
    (by rw [g11_2, show B + 0x21A0 + 0x32C = B + 0x21A0 + BitVec.ofNat 32 0x32C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x5AE (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = op := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = x9 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = L := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = p0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_10 : reg n12 a0 = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x32C = B + 0x21A0 + BitVec.ofNat 32 0x32C by sv_addr, w11_32c]
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m12]; exact w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m12]; exact w11_34
  have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m12]; exact w11_3c
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m12]; exact w11_40
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m12]; exact w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m12]; exact w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
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
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m12]; exact w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m12]; exact w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m12]; exact w11_8c
  have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m12]; exact w11_90
  have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m12]; exact w11_94
  have w12_328 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m12]; exact w11_328
  have w12_32c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m12]; exact w11_32c
  have w12_a20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m12]; exact w11_a20
  have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m12]; exact w11_a24
  have w12_a28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m12]; exact w11_a28
  have w12_a2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m12]; exact w11_a2c
  have w12_a30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m12]; exact w11_a30
  have w12_a34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m12]; exact w11_a34
  have w12_a38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m12]; exact w11_a38
  have w12_a3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m12]; exact w11_a3c
  have w12_a40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m12]; exact w11_a40
  have w12_a44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m12]; exact w11_a44
  have w12_1020 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m12]; exact w11_1020
  have w12_1024 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m12]; exact w11_1024
  clear w11_1024 w11_1020 w11_a44 w11_a40 w11_a3c w11_a38 w11_a34 w11_a30 w11_a2c w11_a28 w11_a24 w11_a20 w11_32c w11_328 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_40 w11_3c w11_34 w11_30 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  by_cases hz_12 : (rem2) - BitVec.ofNat 32 (te8.header + te8.len) = 0
  rotate_left
  · -- 0x5AE: branch, taken
    obtain ⟨n13, d13, u13⟩ := s12.taken E12.self 0xB36 sv_at_5ae
      (by decide) (by rw [g12_10, s12.zero]; exact br_bne_t hz_12)
    have s13 : St n13.mem SV n13 0xB36 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
    have t13 : Steps n0 n13 := t12.trans (.single d13)
    have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
    have E13 : SvCode n13.mem := E12.fr F fr13
    have V13 : SvSaves B n13.mem v := V12.same m13
    have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
    have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
    have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
    have g13_8 : reg n13 (8 : Fin 32) = op := by rw [u13.regs, g12_8]
    have g13_9 : reg n13 (9 : Fin 32) = x9 := by rw [u13.regs, g12_9]
    have g13_10 : reg n13 a0 = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [u13.regs, g12_10]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = L := by rw [u13.regs, g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u13.regs, g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = p0 := by rw [u13.regs, g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u13.regs, g12_27]
    have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m13]; exact w12_30
    have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m13]; exact w12_34
    have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m13]; exact w12_3c
    have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m13]; exact w12_40
    have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m13]; exact w12_48
    have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m13]; exact w12_4c
    have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
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
    have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m13]; exact w12_80
    have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m13]; exact w12_84
    have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m13]; exact w12_88
    have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m13]; exact w12_8c
    have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m13]; exact w12_90
    have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m13]; exact w12_94
    have w13_328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m13]; exact w12_328
    have w13_32c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m13]; exact w12_32c
    have w13_a20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m13]; exact w12_a20
    have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m13]; exact w12_a24
    have w13_a28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m13]; exact w12_a28
    have w13_a2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m13]; exact w12_a2c
    have w13_a30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m13]; exact w12_a30
    have w13_a34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m13]; exact w12_a34
    have w13_a38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m13]; exact w12_a38
    have w13_a3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m13]; exact w12_a3c
    have w13_a40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m13]; exact w12_a40
    have w13_a44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m13]; exact w12_a44
    have w13_1020 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m13]; exact w12_1020
    have w13_1024 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m13]; exact w12_1024
    clear w12_1024 w12_1020 w12_a44 w12_a40 w12_a3c w12_a38 w12_a34 w12_a30 w12_a2c w12_a28 w12_a24 w12_a20 w12_32c w12_328 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_40 w12_3c w12_34 w12_30 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    -- 0xB36
    obtain ⟨n14, c14, u14⟩ := s13.block svX2nb36 E13.self svX2nb36_end
      ⟨trivial, trivial⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have s14 : St n14.mem SV n14 0xB38 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have rb14 : ∀ q, reg n14 q = (runBlock svX2nb36 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
    have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
    have t14 : Steps n0 n14 := t13.trans c14
    have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
    have E14 : SvCode n14.mem := E13.fr F fr14
    have V14 : SvSaves B n14.mem v := V13.same m14
    have g14_2 : reg n14 sp = B + 0x21A0 := by
      rw [rb14, runBlock_reg _ _ _ sp s13.zero (by decide), g13_2]
    have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb14, runBlock_reg _ _ _ (3 : Fin 32) s13.zero (by decide), g13_3]
    have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb14, runBlock_reg _ _ _ (4 : Fin 32) s13.zero (by decide), g13_4]
    have g14_8 : reg n14 (8 : Fin 32) = op := by
      rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
    have g14_9 : reg n14 (9 : Fin 32) = x9 := by
      rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
    have g14_18 : reg n14 (18 : Fin 32) = out := by
      rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by
      rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
    have g14_21 : reg n14 (21 : Fin 32) = x21 := by
      rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
    have g14_22 : reg n14 (22 : Fin 32) = L := by
      rw [rb14, runBlock_reg _ _ _ (22 : Fin 32) s13.zero (by decide), g13_22]
    have g14_23 : reg n14 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb14, runBlock_reg _ _ _ (23 : Fin 32) s13.zero (by decide), g13_23]
    have g14_24 : reg n14 (24 : Fin 32) = p0 := by
      rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = x25 := by
      rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = x26 := by
      rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
    have g14_10 : reg n14 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb14]; simp +decide only [runBlock, BInstr.run, svX2nb36, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_18, g13_19, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m14]; exact w13_30
    have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m14]; exact w13_34
    have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m14]; exact w13_3c
    have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m14]; exact w13_40
    have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m14]; exact w13_48
    have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m14]; exact w13_4c
    have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m14]; exact w13_50
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
    have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m14]; exact w13_80
    have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m14]; exact w13_84
    have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m14]; exact w13_88
    have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m14]; exact w13_8c
    have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m14]; exact w13_90
    have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m14]; exact w13_94
    have w14_328 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m14]; exact w13_328
    have w14_32c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m14]; exact w13_32c
    have w14_a20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m14]; exact w13_a20
    have w14_a24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m14]; exact w13_a24
    have w14_a28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m14]; exact w13_a28
    have w14_a2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m14]; exact w13_a2c
    have w14_a30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m14]; exact w13_a30
    have w14_a34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m14]; exact w13_a34
    have w14_a38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m14]; exact w13_a38
    have w14_a3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m14]; exact w13_a3c
    have w14_a40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m14]; exact w13_a40
    have w14_a44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m14]; exact w13_a44
    have w14_1020 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m14]; exact w13_1020
    have w14_1024 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m14]; exact w13_1024
    clear w13_1024 w13_1020 w13_a44 w13_a40 w13_a3c w13_a38 w13_a34 w13_a30 w13_a2c w13_a28 w13_a24 w13_a20 w13_32c w13_328 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_40 w13_3c w13_34 w13_30 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_19 g13_18 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
    -- 0xB38: sw
    obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sw F E14 s14 sv_at_b38 (off' := 0xB3A) (c := 0x44)
      (by decide) (by rw [g14_2]; sv_addr) (by decide) (by decide)
    have t15 : Steps n0 n15 := t14.trans d15
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
    have g15_8 : reg n15 (8 : Fin 32) = op := by rw [rg15 (8 : Fin 32), g14_8]
    have g15_9 : reg n15 (9 : Fin 32) = x9 := by rw [rg15 (9 : Fin 32), g14_9]
    have g15_10 : reg n15 a0 = BitVec.ofNat 32 0x1 := by rw [rg15 a0, g14_10]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rg15 (18 : Fin 32), g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rg15 (19 : Fin 32), g14_19]
    have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [rg15 (21 : Fin 32), g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = L := by rw [rg15 (22 : Fin 32), g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg15 (23 : Fin 32), g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = p0 := by rw [rg15 (24 : Fin 32), g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [rg15 (25 : Fin 32), g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [rg15 (26 : Fin 32), g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg15 (27 : Fin 32), g14_27]
    have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K15.w32 (by decide) (by decide)).trans w14_30
    have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K15.w32 (by decide) (by decide)).trans w14_34
    have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := (K15.w32 (by decide) (by decide)).trans w14_3c
    have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K15.w32 (by decide) (by decide)).trans w14_40
    have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K15.w32 (by decide) (by decide)).trans w14_48
    have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K15.w32 (by decide) (by decide)).trans w14_4c
    have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K15.w32 (by decide) (by decide)).trans w14_50
    have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K15.w32 (by decide) (by decide)).trans w14_54
    have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K15.w32 (by decide) (by decide)).trans w14_58
    have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K15.w32 (by decide) (by decide)).trans w14_5c
    have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K15.w32 (by decide) (by decide)).trans w14_60
    have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K15.w32 (by decide) (by decide)).trans w14_64
    have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K15.w32 (by decide) (by decide)).trans w14_68
    have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K15.w32 (by decide) (by decide)).trans w14_6c
    have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K15.w32 (by decide) (by decide)).trans w14_70
    have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K15.w32 (by decide) (by decide)).trans w14_74
    have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K15.w32 (by decide) (by decide)).trans w14_78
    have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K15.w32 (by decide) (by decide)).trans w14_7c
    have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K15.w32 (by decide) (by decide)).trans w14_80
    have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K15.w32 (by decide) (by decide)).trans w14_84
    have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K15.w32 (by decide) (by decide)).trans w14_88
    have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K15.w32 (by decide) (by decide)).trans w14_8c
    have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K15.w32 (by decide) (by decide)).trans w14_90
    have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K15.w32 (by decide) (by decide)).trans w14_94
    have w15_328 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := (K15.w32 (by decide) (by decide)).trans w14_328
    have w15_32c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := (K15.w32 (by decide) (by decide)).trans w14_32c
    have w15_a20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K15.w32 (by decide) (by decide)).trans w14_a20
    have w15_a24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K15.w32 (by decide) (by decide)).trans w14_a24
    have w15_a28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K15.w32 (by decide) (by decide)).trans w14_a28
    have w15_a2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K15.w32 (by decide) (by decide)).trans w14_a2c
    have w15_a30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K15.w32 (by decide) (by decide)).trans w14_a30
    have w15_a34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K15.w32 (by decide) (by decide)).trans w14_a34
    have w15_a38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K15.w32 (by decide) (by decide)).trans w14_a38
    have w15_a3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K15.w32 (by decide) (by decide)).trans w14_a3c
    have w15_a40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K15.w32 (by decide) (by decide)).trans w14_a40
    have w15_a44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K15.w32 (by decide) (by decide)).trans w14_a44
    have w15_1020 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := (K15.w32 (by decide) (by decide)).trans w14_1020
    have w15_1024 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := (K15.w32 (by decide) (by decide)).trans w14_1024
    have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [W15, g14_10]
    clear w14_1024 w14_1020 w14_a44 w14_a40 w14_a3c w14_a38 w14_a34 w14_a30 w14_a2c w14_a28 w14_a24 w14_a20 w14_32c w14_328 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_40 w14_3c w14_34 w14_30 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
    -- 0xB3A: j
    obtain ⟨n16, d16, u16⟩ := s15.jump E15.self sv_at_b3a (off' := 0xB46) (by decide)
      (by rw [s15.pc]; decide)
    have s16 : St n16.mem SV n16 0xB46 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
    have g16_8 : reg n16 (8 : Fin 32) = op := by rw [u16.regs, g15_8]
    have g16_9 : reg n16 (9 : Fin 32) = x9 := by rw [u16.regs, g15_9]
    have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x1 := by rw [u16.regs, g15_10]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
    have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = L := by rw [u16.regs, g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u16.regs, g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = p0 := by rw [u16.regs, g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, g15_27]
    have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m16]; exact w15_30
    have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m16]; exact w15_34
    have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m16]; exact w15_3c
    have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m16]; exact w15_40
    have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m16]; exact w15_44
    have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m16]; exact w15_48
    have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m16]; exact w15_4c
    have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
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
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m16]; exact w15_80
    have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m16]; exact w15_84
    have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m16]; exact w15_88
    have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m16]; exact w15_8c
    have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m16]; exact w15_90
    have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m16]; exact w15_94
    have w16_328 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m16]; exact w15_328
    have w16_32c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m16]; exact w15_32c
    have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m16]; exact w15_a20
    have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m16]; exact w15_a24
    have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m16]; exact w15_a28
    have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m16]; exact w15_a2c
    have w16_a30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m16]; exact w15_a30
    have w16_a34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m16]; exact w15_a34
    have w16_a38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m16]; exact w15_a38
    have w16_a3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m16]; exact w15_a3c
    have w16_a40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m16]; exact w15_a40
    have w16_a44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m16]; exact w15_a44
    have w16_1020 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m16]; exact w15_1020
    have w16_1024 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m16]; exact w15_1024
    clear w15_44 w15_1024 w15_1020 w15_a44 w15_a40 w15_a3c w15_a38 w15_a34 w15_a30 w15_a2c w15_a28 w15_a24 w15_a20 w15_32c w15_328 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_40 w15_3c w15_34 w15_30 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
    -- 0xB46: lw
    obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_b46 (off' := 0xB48) (by decide)
      (by rw [g16_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s17 : St n17.mem SV n17 0xB48 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = op := by rw [u17.regs, upd_ne (by decide) (by decide), g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = x9 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_9]
    have g17_10 : reg n17 a0 = BitVec.ofNat 32 0x1 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_10]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
    have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = L := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = p0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
    have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m17]; exact w16_30
    have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m17]; exact w16_34
    have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m17]; exact w16_3c
    have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m17]; exact w16_40
    have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m17]; exact w16_44
    have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m17]; exact w16_48
    have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m17]; exact w16_4c
    have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
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
    have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m17]; exact w16_80
    have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m17]; exact w16_84
    have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m17]; exact w16_88
    have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m17]; exact w16_8c
    have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m17]; exact w16_90
    have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m17]; exact w16_94
    have w17_328 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m17]; exact w16_328
    have w17_32c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m17]; exact w16_32c
    have w17_a20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m17]; exact w16_a20
    have w17_a24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m17]; exact w16_a24
    have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m17]; exact w16_a28
    have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m17]; exact w16_a2c
    have w17_a30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m17]; exact w16_a30
    have w17_a34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m17]; exact w16_a34
    have w17_a38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m17]; exact w16_a38
    have w17_a3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m17]; exact w16_a3c
    have w17_a40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m17]; exact w16_a40
    have w17_a44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m17]; exact w16_a44
    have w17_1020 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m17]; exact w16_1020
    have w17_1024 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m17]; exact w16_1024
    clear w16_1024 w16_1020 w16_a44 w16_a40 w16_a3c w16_a38 w16_a34 w16_a30 w16_a2c w16_a28 w16_a24 w16_a20 w16_32c w16_328 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_34 w16_30 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_19 g16_18 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    -- 0xB48: j
    obtain ⟨n18, d18, u18⟩ := s17.jump E17.self sv_at_b48 (off' := 0x966) (by decide)
      (by rw [s17.pc]; decide)
    have s18 : St n18.mem SV n18 0x966 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
    have g18_8 : reg n18 (8 : Fin 32) = op := by rw [u18.regs, g17_8]
    have g18_9 : reg n18 (9 : Fin 32) = x9 := by rw [u18.regs, g17_9]
    have g18_10 : reg n18 a0 = BitVec.ofNat 32 0x1 := by rw [u18.regs, g17_10]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
    have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = L := by rw [u18.regs, g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u18.regs, g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = p0 := by rw [u18.regs, g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, g17_27]
    have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m18]; exact w17_30
    have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m18]; exact w17_34
    have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m18]; exact w17_3c
    have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m18]; exact w17_40
    have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m18]; exact w17_44
    have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m18]; exact w17_48
    have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m18]; exact w17_4c
    have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
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
    have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m18]; exact w17_80
    have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m18]; exact w17_84
    have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m18]; exact w17_88
    have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m18]; exact w17_8c
    have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m18]; exact w17_90
    have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m18]; exact w17_94
    have w18_328 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m18]; exact w17_328
    have w18_32c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m18]; exact w17_32c
    have w18_a20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m18]; exact w17_a20
    have w18_a24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m18]; exact w17_a24
    have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m18]; exact w17_a28
    have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m18]; exact w17_a2c
    have w18_a30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m18]; exact w17_a30
    have w18_a34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m18]; exact w17_a34
    have w18_a38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m18]; exact w17_a38
    have w18_a3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m18]; exact w17_a3c
    have w18_a40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m18]; exact w17_a40
    have w18_a44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m18]; exact w17_a44
    have w18_1020 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m18]; exact w17_1020
    have w18_1024 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m18]; exact w17_1024
    clear w17_1024 w17_1020 w17_a44 w17_a40 w17_a3c w17_a38 w17_a34 w17_a30 w17_a2c w17_a28 w17_a24 w17_a20 w17_32c w17_328 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_34 w17_30 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_19 g17_18 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
    exact .inl ⟨(fun ⟨vp8', vl8', h0', te8', h1', h2', _⟩ => by rw [hr8] at h0'; cases h0'; rw [ht8] at h1'; cases h1'; exact hz_12 h2'), sv_fail F E18 s18 t18 (fun x hx => (fR18 x hx).trans (fM x hx).symm) V18 hret g18_2 g18_18 hO g18_3 g18_4⟩
  -- 0x5AE: branch, not taken
  obtain ⟨n13, d13, u13⟩ := s12.notTaken E12.self 0x5B2 sv_at_5ae
    (by decide) (by rw [g12_10, s12.zero]; exact br_bne_f hz_12)
  have s13 : St n13.mem SV n13 0x5B2 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = op := by rw [u13.regs, g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = x9 := by rw [u13.regs, g12_9]
  have g13_10 : reg n13 a0 = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [u13.regs, g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = L := by rw [u13.regs, g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u13.regs, g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = p0 := by rw [u13.regs, g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u13.regs, g12_27]
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m13]; exact w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m13]; exact w12_34
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m13]; exact w12_3c
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m13]; exact w12_40
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m13]; exact w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m13]; exact w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
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
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m13]; exact w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m13]; exact w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m13]; exact w12_8c
  have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m13]; exact w12_90
  have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m13]; exact w12_94
  have w13_328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m13]; exact w12_328
  have w13_32c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m13]; exact w12_32c
  have w13_a20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m13]; exact w12_a20
  have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m13]; exact w12_a24
  have w13_a28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m13]; exact w12_a28
  have w13_a2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m13]; exact w12_a2c
  have w13_a30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m13]; exact w12_a30
  have w13_a34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m13]; exact w12_a34
  have w13_a38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m13]; exact w12_a38
  have w13_a3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m13]; exact w12_a3c
  have w13_a40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m13]; exact w12_a40
  have w13_a44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m13]; exact w12_a44
  have w13_1020 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m13]; exact w12_1020
  have w13_1024 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m13]; exact w12_1024
  clear w12_1024 w12_1020 w12_a44 w12_a40 w12_a3c w12_a38 w12_a34 w12_a30 w12_a2c w12_a28 w12_a24 w12_a20 w12_32c w12_328 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_40 w12_3c w12_34 w12_30 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x5B2: lw
  obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_5b2 (off' := 0x5B6) (by decide)
    (by rw [g13_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x604 = B + 0x21A0 + BitVec.ofNat 32 0x1024 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s14 : St n14.mem SV n14 0x5B6 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = op := by rw [u14.regs, upd_ne (by decide) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = x9 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, upd_ne (by decide) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_19]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = L := by rw [u14.regs, upd_ne (by decide) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = p0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_27]
  have g14_10 : reg n14 a0 = vl8 := by
    rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g13_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x604 = B + 0x21A0 + BitVec.ofNat 32 0x1024 by sv_addr, w13_1024]
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m14]; exact w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m14]; exact w13_34
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m14]; exact w13_3c
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m14]; exact w13_40
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m14]; exact w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m14]; exact w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m14]; exact w13_50
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
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m14]; exact w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m14]; exact w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m14]; exact w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m14]; exact w13_8c
  have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m14]; exact w13_90
  have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m14]; exact w13_94
  have w14_328 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m14]; exact w13_328
  have w14_32c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m14]; exact w13_32c
  have w14_a20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m14]; exact w13_a20
  have w14_a24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m14]; exact w13_a24
  have w14_a28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m14]; exact w13_a28
  have w14_a2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m14]; exact w13_a2c
  have w14_a30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m14]; exact w13_a30
  have w14_a34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m14]; exact w13_a34
  have w14_a38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m14]; exact w13_a38
  have w14_a3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m14]; exact w13_a3c
  have w14_a40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m14]; exact w13_a40
  have w14_a44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m14]; exact w13_a44
  have w14_1020 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m14]; exact w13_1020
  have w14_1024 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m14]; exact w13_1024
  clear w13_1024 w13_1020 w13_a44 w13_a40 w13_a3c w13_a38 w13_a34 w13_a30 w13_a2c w13_a28 w13_a24 w13_a20 w13_32c w13_328 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_40 w13_3c w13_34 w13_30 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_19 g13_18 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0x5B6: sw
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sw F E14 s14 sv_at_5b6 (off' := 0x5B8) (c := 0x38)
    (by decide) (by rw [g14_2]; sv_addr) (by decide) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = op := by rw [rg15 (8 : Fin 32), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = x9 := by rw [rg15 (9 : Fin 32), g14_9]
  have g15_10 : reg n15 a0 = vl8 := by rw [rg15 a0, g14_10]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rg15 (18 : Fin 32), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rg15 (19 : Fin 32), g14_19]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [rg15 (21 : Fin 32), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = L := by rw [rg15 (22 : Fin 32), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg15 (23 : Fin 32), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = p0 := by rw [rg15 (24 : Fin 32), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [rg15 (25 : Fin 32), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [rg15 (26 : Fin 32), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg15 (27 : Fin 32), g14_27]
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K15.w32 (by decide) (by decide)).trans w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K15.w32 (by decide) (by decide)).trans w14_34
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := (K15.w32 (by decide) (by decide)).trans w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K15.w32 (by decide) (by decide)).trans w14_40
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K15.w32 (by decide) (by decide)).trans w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K15.w32 (by decide) (by decide)).trans w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K15.w32 (by decide) (by decide)).trans w14_50
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K15.w32 (by decide) (by decide)).trans w14_54
  have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K15.w32 (by decide) (by decide)).trans w14_58
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K15.w32 (by decide) (by decide)).trans w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K15.w32 (by decide) (by decide)).trans w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K15.w32 (by decide) (by decide)).trans w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K15.w32 (by decide) (by decide)).trans w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K15.w32 (by decide) (by decide)).trans w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K15.w32 (by decide) (by decide)).trans w14_70
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K15.w32 (by decide) (by decide)).trans w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K15.w32 (by decide) (by decide)).trans w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K15.w32 (by decide) (by decide)).trans w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K15.w32 (by decide) (by decide)).trans w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K15.w32 (by decide) (by decide)).trans w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K15.w32 (by decide) (by decide)).trans w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K15.w32 (by decide) (by decide)).trans w14_8c
  have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K15.w32 (by decide) (by decide)).trans w14_90
  have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K15.w32 (by decide) (by decide)).trans w14_94
  have w15_328 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := (K15.w32 (by decide) (by decide)).trans w14_328
  have w15_32c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := (K15.w32 (by decide) (by decide)).trans w14_32c
  have w15_a20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K15.w32 (by decide) (by decide)).trans w14_a20
  have w15_a24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K15.w32 (by decide) (by decide)).trans w14_a24
  have w15_a28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K15.w32 (by decide) (by decide)).trans w14_a28
  have w15_a2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K15.w32 (by decide) (by decide)).trans w14_a2c
  have w15_a30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K15.w32 (by decide) (by decide)).trans w14_a30
  have w15_a34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K15.w32 (by decide) (by decide)).trans w14_a34
  have w15_a38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K15.w32 (by decide) (by decide)).trans w14_a38
  have w15_a3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K15.w32 (by decide) (by decide)).trans w14_a3c
  have w15_a40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K15.w32 (by decide) (by decide)).trans w14_a40
  have w15_a44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K15.w32 (by decide) (by decide)).trans w14_a44
  have w15_1020 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := (K15.w32 (by decide) (by decide)).trans w14_1020
  have w15_1024 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := (K15.w32 (by decide) (by decide)).trans w14_1024
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [W15, g14_10]
  clear w14_1024 w14_1020 w14_a44 w14_a40 w14_a3c w14_a38 w14_a34 w14_a30 w14_a2c w14_a28 w14_a24 w14_a20 w14_32c w14_328 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_40 w14_3c w14_34 w14_30 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0x5B8: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_5b8 (off' := 0x5BA) (by decide)
    (by rw [g15_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s16 : St n16.mem SV n16 0x5BA (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = op := by rw [u16.regs, upd_ne (by decide) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = x9 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = L := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = p0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
  have g16_10 : reg n16 a0 = rem := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr, w15_40]
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m16]; exact w15_30
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m16]; exact w15_34
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m16]; exact w15_38
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m16]; exact w15_3c
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m16]; exact w15_40
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m16]; exact w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m16]; exact w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
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
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m16]; exact w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m16]; exact w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m16]; exact w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m16]; exact w15_8c
  have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m16]; exact w15_90
  have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m16]; exact w15_94
  have w16_328 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m16]; exact w15_328
  have w16_32c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m16]; exact w15_32c
  have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m16]; exact w15_a20
  have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m16]; exact w15_a24
  have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m16]; exact w15_a28
  have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m16]; exact w15_a2c
  have w16_a30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m16]; exact w15_a30
  have w16_a34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m16]; exact w15_a34
  have w16_a38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m16]; exact w15_a38
  have w16_a3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m16]; exact w15_a3c
  have w16_a40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m16]; exact w15_a40
  have w16_a44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m16]; exact w15_a44
  have w16_1020 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m16]; exact w15_1020
  have w16_1024 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m16]; exact w15_1024
  clear w15_38 w15_1024 w15_1020 w15_a44 w15_a40 w15_a3c w15_a38 w15_a34 w15_a30 w15_a2c w15_a28 w15_a24 w15_a20 w15_32c w15_328 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_40 w15_3c w15_34 w15_30 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  -- 0x5BA
  obtain ⟨n17, c17, u17⟩ := s16.block svX2n5ba E16.self svX2n5ba_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x5C2 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svX2n5ba (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans c17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by
    rw [rb17, runBlock_reg _ _ _ sp s16.zero (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (3 : Fin 32) s16.zero (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (4 : Fin 32) s16.zero (by decide), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = op := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = x9 := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = L := by
    rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = p0 := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = p0 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svX2n5ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_18, g16_19, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_11 : reg n17 a1 = (L) - (rem) := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svX2n5ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_18, g16_19, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_12 : reg n17 a2 = op := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svX2n5ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_18, g16_19, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m17]; exact w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m17]; exact w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m17]; exact w16_38
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m17]; exact w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m17]; exact w16_40
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m17]; exact w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m17]; exact w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
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
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m17]; exact w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m17]; exact w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m17]; exact w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m17]; exact w16_8c
  have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m17]; exact w16_90
  have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m17]; exact w16_94
  have w17_328 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m17]; exact w16_328
  have w17_32c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m17]; exact w16_32c
  have w17_a20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m17]; exact w16_a20
  have w17_a24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m17]; exact w16_a24
  have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m17]; exact w16_a28
  have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m17]; exact w16_a2c
  have w17_a30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m17]; exact w16_a30
  have w17_a34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m17]; exact w16_a34
  have w17_a38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m17]; exact w16_a38
  have w17_a3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m17]; exact w16_a3c
  have w17_a40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m17]; exact w16_a40
  have w17_a44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m17]; exact w16_a44
  have w17_1020 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m17]; exact w16_1020
  have w17_1024 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m17]; exact w16_1024
  clear w16_1024 w16_1020 w16_a44 w16_a40 w16_a3c w16_a38 w16_a34 w16_a30 w16_a2c w16_a28 w16_a24 w16_a20 w16_32c w16_328 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_40 w16_3c w16_38 w16_34 w16_30 g16_10 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  rw [sub_ofNat_toNat hle] at g17_11
  -- 0x5C2: lw
  obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_5c2 (off' := 0x5C4) (by decide)
    (by rw [g17_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s18 : St n18.mem SV n18 0x5C4 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = op := by rw [u18.regs, upd_ne (by decide) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = x9 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_9]
  have g18_10 : reg n18 a0 = p0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_10]
  have g18_11 : reg n18 a1 = BitVec.ofNat 32 (L.toNat - rem.toNat) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_11]
  have g18_12 : reg n18 a2 = op := by rw [u18.regs, upd_ne (by decide) (by decide), g17_12]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = L := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = p0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
  have g18_13 : reg n18 a3 = ol := by
    rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g17_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w17_48]
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m18]; exact w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m18]; exact w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m18]; exact w17_38
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m18]; exact w17_3c
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m18]; exact w17_40
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m18]; exact w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m18]; exact w17_4c
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
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
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m18]; exact w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m18]; exact w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m18]; exact w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m18]; exact w17_8c
  have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m18]; exact w17_90
  have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m18]; exact w17_94
  have w18_328 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m18]; exact w17_328
  have w18_32c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m18]; exact w17_32c
  have w18_a20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m18]; exact w17_a20
  have w18_a24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m18]; exact w17_a24
  have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m18]; exact w17_a28
  have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m18]; exact w17_a2c
  have w18_a30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m18]; exact w17_a30
  have w18_a34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m18]; exact w17_a34
  have w18_a38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m18]; exact w17_a38
  have w18_a3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m18]; exact w17_a3c
  have w18_a40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m18]; exact w17_a40
  have w18_a44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m18]; exact w17_a44
  have w18_1020 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m18]; exact w17_1020
  have w18_1024 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m18]; exact w17_1024
  clear w17_1024 w17_1020 w17_a44 w17_a40 w17_a3c w17_a38 w17_a34 w17_a30 w17_a2c w17_a28 w17_a24 w17_a20 w17_32c w17_328 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_40 w17_3c w17_38 w17_34 w17_30 g17_12 g17_11 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x5C4: sv_loF
  obtain ⟨n19, c19, s19, sp19, rk19, R19, K19, fr19⟩ := sv_loF (nl := L.toNat - rem.toNat) (ql := ol.toNat)
    F E18 s18 sv_at_5c4 sv_at_5c8 (by decide) (by decide) g18_2
    g18_10 g18_11 g18_12 (by rw [g18_13, ofNat_toNat_self]) ea_in oid_in
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keepL K19 (by decide)
  rw [listsOidOf, listsOidLoop_congr _ _ _ (sv_pt fR18 ea_in), sv_mb fR18 oid_in, ← listsOidOf] at R19
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk19 (3 : Fin 32) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk19 (4 : Fin 32) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = op := by rw [rk19 (8 : Fin 32) (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = x9 := by rw [rk19 (9 : Fin 32) (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rk19 (18 : Fin 32) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rk19 (19 : Fin 32) (by decide), g18_19]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [rk19 (21 : Fin 32) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = L := by rw [rk19 (22 : Fin 32) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rk19 (23 : Fin 32) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = p0 := by rw [rk19 (24 : Fin 32) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [rk19 (25 : Fin 32) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [rk19 (26 : Fin 32) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk19 (27 : Fin 32) (by decide), g18_27]
  have g19_2 : reg n19 sp = B + 0x21A0 := sp19
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K19.w32 (by decide) (by decide)).trans w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K19.w32 (by decide) (by decide)).trans w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := (K19.w32 (by decide) (by decide)).trans w18_38
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := (K19.w32 (by decide) (by decide)).trans w18_3c
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K19.w32 (by decide) (by decide)).trans w18_40
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K19.w32 (by decide) (by decide)).trans w18_48
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K19.w32 (by decide) (by decide)).trans w18_4c
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K19.w32 (by decide) (by decide)).trans w18_50
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
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K19.w32 (by decide) (by decide)).trans w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K19.w32 (by decide) (by decide)).trans w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K19.w32 (by decide) (by decide)).trans w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K19.w32 (by decide) (by decide)).trans w18_8c
  have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K19.w32 (by decide) (by decide)).trans w18_90
  have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K19.w32 (by decide) (by decide)).trans w18_94
  have w19_328 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := (K19.w32 (by decide) (by decide)).trans w18_328
  have w19_32c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := (K19.w32 (by decide) (by decide)).trans w18_32c
  have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K19.w32 (by decide) (by decide)).trans w18_a20
  have w19_a24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K19.w32 (by decide) (by decide)).trans w18_a24
  have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K19.w32 (by decide) (by decide)).trans w18_a28
  have w19_a2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K19.w32 (by decide) (by decide)).trans w18_a2c
  have w19_a30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K19.w32 (by decide) (by decide)).trans w18_a30
  have w19_a34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K19.w32 (by decide) (by decide)).trans w18_a34
  have w19_a38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K19.w32 (by decide) (by decide)).trans w18_a38
  have w19_a3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K19.w32 (by decide) (by decide)).trans w18_a3c
  have w19_a40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K19.w32 (by decide) (by decide)).trans w18_a40
  have w19_a44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K19.w32 (by decide) (by decide)).trans w18_a44
  have w19_1020 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := (K19.w32 (by decide) (by decide)).trans w18_1020
  have w19_1024 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := (K19.w32 (by decide) (by decide)).trans w18_1024
  clear w18_1024 w18_1020 w18_a44 w18_a40 w18_a3c w18_a38 w18_a34 w18_a30 w18_a2c w18_a28 w18_a24 w18_a20 w18_32c w18_328 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_40 w18_3c w18_38 w18_34 w18_30 g18_13 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_19 g18_18 g18_12 g18_11 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  obtain ⟨r19, hr19⟩ : ∃ r, listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op ol.toNat) = r := ⟨_, rfl⟩
  rcases r19 with lb19 | (_ | _)
  · rw [hr19] at R19
    obtain ⟨a0_19, a1_19⟩ := R19
    have g19_10 : reg n19 a0 = BitVec.ofNat 32 0x1 := a0_19
    have g19_11 : reg n19 a1 = (lb19).zeroExtend 32 := a1_19
    -- 0x5CC
    obtain ⟨n20, c20, u20⟩ := s19.block svX2n5cc E19.self svX2n5cc_end
      ⟨trivial, trivial⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have s20 : St n20.mem SV n20 0x5CE (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have rb20 : ∀ q, reg n20 q = (runBlock svX2n5cc (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
    have g20_8 : reg n20 (8 : Fin 32) = op := by
      rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
    have g20_9 : reg n20 (9 : Fin 32) = x9 := by
      rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
    have g20_11 : reg n20 a1 = (lb19).zeroExtend 32 := by
      rw [rb20, runBlock_reg _ _ _ a1 s19.zero (by decide), g19_11]
    have g20_18 : reg n20 (18 : Fin 32) = out := by
      rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by
      rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
    have g20_21 : reg n20 (21 : Fin 32) = x21 := by
      rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = L := by
      rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = p0 := by
      rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = x25 := by
      rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = x26 := by
      rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
    have g20_10 : reg n20 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb20]; simp +decide only [runBlock, BInstr.run, svX2n5cc, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_11, g19_18, g19_19, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m20]; exact w19_30
    have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m20]; exact w19_34
    have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m20]; exact w19_38
    have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m20]; exact w19_3c
    have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m20]; exact w19_40
    have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m20]; exact w19_48
    have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m20]; exact w19_4c
    have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
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
    have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m20]; exact w19_80
    have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m20]; exact w19_84
    have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m20]; exact w19_88
    have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m20]; exact w19_8c
    have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m20]; exact w19_90
    have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m20]; exact w19_94
    have w20_328 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m20]; exact w19_328
    have w20_32c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m20]; exact w19_32c
    have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m20]; exact w19_a20
    have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m20]; exact w19_a24
    have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m20]; exact w19_a28
    have w20_a2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m20]; exact w19_a2c
    have w20_a30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m20]; exact w19_a30
    have w20_a34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m20]; exact w19_a34
    have w20_a38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m20]; exact w19_a38
    have w20_a3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m20]; exact w19_a3c
    have w20_a40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m20]; exact w19_a40
    have w20_a44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m20]; exact w19_a44
    have w20_1020 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m20]; exact w19_1020
    have w20_1024 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m20]; exact w19_1024
    clear w19_1024 w19_1020 w19_a44 w19_a40 w19_a3c w19_a38 w19_a34 w19_a30 w19_a2c w19_a28 w19_a24 w19_a20 w19_32c w19_328 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_40 w19_3c w19_38 w19_34 w19_30 g19_2 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 V19 E19 fR19 t19 fr19 K19 rk19 sp19 s19 c19
    -- 0x5CE: sw
    obtain ⟨n21, d21, s21, fr21, K21, W21, rg21⟩ := sv_sw F E20 s20 sv_at_5ce (off' := 0x5D0) (c := 0x44)
      (by decide) (by rw [g20_2]; sv_addr) (by decide) (by decide)
    have t21 : Steps n0 n21 := t20.trans d21
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.keep K21 (by decide)
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rg21 sp, g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg21 (3 : Fin 32), g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg21 (4 : Fin 32), g20_4]
    have g21_8 : reg n21 (8 : Fin 32) = op := by rw [rg21 (8 : Fin 32), g20_8]
    have g21_9 : reg n21 (9 : Fin 32) = x9 := by rw [rg21 (9 : Fin 32), g20_9]
    have g21_10 : reg n21 a0 = BitVec.ofNat 32 0x1 := by rw [rg21 a0, g20_10]
    have g21_11 : reg n21 a1 = (lb19).zeroExtend 32 := by rw [rg21 a1, g20_11]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rg21 (18 : Fin 32), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rg21 (19 : Fin 32), g20_19]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [rg21 (21 : Fin 32), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = L := by rw [rg21 (22 : Fin 32), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg21 (23 : Fin 32), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = p0 := by rw [rg21 (24 : Fin 32), g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [rg21 (25 : Fin 32), g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [rg21 (26 : Fin 32), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg21 (27 : Fin 32), g20_27]
    have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K21.w32 (by decide) (by decide)).trans w20_30
    have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K21.w32 (by decide) (by decide)).trans w20_34
    have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := (K21.w32 (by decide) (by decide)).trans w20_38
    have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := (K21.w32 (by decide) (by decide)).trans w20_3c
    have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K21.w32 (by decide) (by decide)).trans w20_40
    have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K21.w32 (by decide) (by decide)).trans w20_48
    have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K21.w32 (by decide) (by decide)).trans w20_4c
    have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K21.w32 (by decide) (by decide)).trans w20_50
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
    have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K21.w32 (by decide) (by decide)).trans w20_80
    have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K21.w32 (by decide) (by decide)).trans w20_84
    have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K21.w32 (by decide) (by decide)).trans w20_88
    have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K21.w32 (by decide) (by decide)).trans w20_8c
    have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K21.w32 (by decide) (by decide)).trans w20_90
    have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K21.w32 (by decide) (by decide)).trans w20_94
    have w21_328 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := (K21.w32 (by decide) (by decide)).trans w20_328
    have w21_32c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := (K21.w32 (by decide) (by decide)).trans w20_32c
    have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K21.w32 (by decide) (by decide)).trans w20_a20
    have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K21.w32 (by decide) (by decide)).trans w20_a24
    have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K21.w32 (by decide) (by decide)).trans w20_a28
    have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K21.w32 (by decide) (by decide)).trans w20_a2c
    have w21_a30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K21.w32 (by decide) (by decide)).trans w20_a30
    have w21_a34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K21.w32 (by decide) (by decide)).trans w20_a34
    have w21_a38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K21.w32 (by decide) (by decide)).trans w20_a38
    have w21_a3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K21.w32 (by decide) (by decide)).trans w20_a3c
    have w21_a40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K21.w32 (by decide) (by decide)).trans w20_a40
    have w21_a44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K21.w32 (by decide) (by decide)).trans w20_a44
    have w21_1020 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := (K21.w32 (by decide) (by decide)).trans w20_1020
    have w21_1024 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := (K21.w32 (by decide) (by decide)).trans w20_1024
    have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (lb19).zeroExtend 32 := by rw [W21, g20_11]
    clear w20_1024 w20_1020 w20_a44 w20_a40 w20_a3c w20_a38 w20_a34 w20_a30 w20_a2c w20_a28 w20_a24 w20_a20 w20_32c w20_328 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_40 w20_3c w20_38 w20_34 w20_30 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_11 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20 g19_11 g19_10 a1_19 a0_19
    -- 0x5D0: branch, taken
    obtain ⟨n22, d22, u22⟩ := s21.taken E21.self 0xB46 sv_at_5d0
      (by decide) (by rw [g21_10, s21.zero]; decide)
    have s22 : St n22.mem SV n22 0xB46 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = op := by rw [u22.regs, g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = x9 := by rw [u22.regs, g21_9]
    have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x1 := by rw [u22.regs, g21_10]
    have g22_11 : reg n22 a1 = (lb19).zeroExtend 32 := by rw [u22.regs, g21_11]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = L := by rw [u22.regs, g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = p0 := by rw [u22.regs, g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u22.regs, g21_27]
    have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m22]; exact w21_30
    have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m22]; exact w21_34
    have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m22]; exact w21_38
    have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m22]; exact w21_3c
    have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m22]; exact w21_40
    have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (lb19).zeroExtend 32 := by rw [m22]; exact w21_44
    have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m22]; exact w21_48
    have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m22]; exact w21_4c
    have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m22]; exact w21_50
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
    have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m22]; exact w21_80
    have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m22]; exact w21_84
    have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m22]; exact w21_88
    have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m22]; exact w21_8c
    have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m22]; exact w21_90
    have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m22]; exact w21_94
    have w22_328 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m22]; exact w21_328
    have w22_32c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m22]; exact w21_32c
    have w22_a20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m22]; exact w21_a20
    have w22_a24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m22]; exact w21_a24
    have w22_a28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m22]; exact w21_a28
    have w22_a2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m22]; exact w21_a2c
    have w22_a30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m22]; exact w21_a30
    have w22_a34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m22]; exact w21_a34
    have w22_a38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m22]; exact w21_a38
    have w22_a3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m22]; exact w21_a3c
    have w22_a40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m22]; exact w21_a40
    have w22_a44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m22]; exact w21_a44
    have w22_1020 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m22]; exact w21_1020
    have w22_1024 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m22]; exact w21_1024
    clear w21_44 w21_1024 w21_1020 w21_a44 w21_a40 w21_a3c w21_a38 w21_a34 w21_a30 w21_a2c w21_a28 w21_a24 w21_a20 w21_32c w21_328 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_40 w21_3c w21_38 w21_34 w21_30 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_19 g21_18 g21_11 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 rg21 W21 K21 fr21 s21 d21
    -- 0xB46: lw
    obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_b46 (off' := 0xB48) (by decide)
      (by rw [g22_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s23 : St n23.mem SV n23 0xB48 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
    have t23 : Steps n0 n23 := t22.trans (.single d23)
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.same m23
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
    have g23_8 : reg n23 (8 : Fin 32) = op := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
    have g23_9 : reg n23 (9 : Fin 32) = x9 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
    have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x1 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_10]
    have g23_11 : reg n23 a1 = (lb19).zeroExtend 32 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_11]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
    have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = L := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = p0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
    have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m23]; exact w22_30
    have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m23]; exact w22_34
    have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m23]; exact w22_38
    have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m23]; exact w22_3c
    have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m23]; exact w22_40
    have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (lb19).zeroExtend 32 := by rw [m23]; exact w22_44
    have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m23]; exact w22_48
    have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m23]; exact w22_4c
    have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
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
    have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m23]; exact w22_80
    have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m23]; exact w22_84
    have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m23]; exact w22_88
    have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m23]; exact w22_8c
    have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m23]; exact w22_90
    have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m23]; exact w22_94
    have w23_328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m23]; exact w22_328
    have w23_32c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m23]; exact w22_32c
    have w23_a20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m23]; exact w22_a20
    have w23_a24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m23]; exact w22_a24
    have w23_a28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m23]; exact w22_a28
    have w23_a2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m23]; exact w22_a2c
    have w23_a30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m23]; exact w22_a30
    have w23_a34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m23]; exact w22_a34
    have w23_a38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m23]; exact w22_a38
    have w23_a3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m23]; exact w22_a3c
    have w23_a40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m23]; exact w22_a40
    have w23_a44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m23]; exact w22_a44
    have w23_1020 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m23]; exact w22_1020
    have w23_1024 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m23]; exact w22_1024
    clear w22_1024 w22_1020 w22_a44 w22_a40 w22_a3c w22_a38 w22_a34 w22_a30 w22_a2c w22_a28 w22_a24 w22_a20 w22_32c w22_328 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_19 g22_18 g22_11 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    -- 0xB48: j
    obtain ⟨n24, d24, u24⟩ := s23.jump E23.self sv_at_b48 (off' := 0x966) (by decide)
      (by rw [s23.pc]; decide)
    have s24 : St n24.mem SV n24 0x966 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
    have g24_8 : reg n24 (8 : Fin 32) = op := by rw [u24.regs, g23_8]
    have g24_9 : reg n24 (9 : Fin 32) = x9 := by rw [u24.regs, g23_9]
    have g24_10 : reg n24 a0 = BitVec.ofNat 32 0x1 := by rw [u24.regs, g23_10]
    have g24_11 : reg n24 a1 = (lb19).zeroExtend 32 := by rw [u24.regs, g23_11]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
    have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = L := by rw [u24.regs, g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u24.regs, g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = p0 := by rw [u24.regs, g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u24.regs, g23_27]
    have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m24]; exact w23_30
    have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m24]; exact w23_34
    have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m24]; exact w23_38
    have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m24]; exact w23_3c
    have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m24]; exact w23_40
    have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (lb19).zeroExtend 32 := by rw [m24]; exact w23_44
    have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m24]; exact w23_48
    have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m24]; exact w23_4c
    have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
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
    have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m24]; exact w23_80
    have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m24]; exact w23_84
    have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m24]; exact w23_88
    have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m24]; exact w23_8c
    have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m24]; exact w23_90
    have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m24]; exact w23_94
    have w24_328 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m24]; exact w23_328
    have w24_32c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m24]; exact w23_32c
    have w24_a20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m24]; exact w23_a20
    have w24_a24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m24]; exact w23_a24
    have w24_a28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m24]; exact w23_a28
    have w24_a2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m24]; exact w23_a2c
    have w24_a30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m24]; exact w23_a30
    have w24_a34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m24]; exact w23_a34
    have w24_a38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m24]; exact w23_a38
    have w24_a3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m24]; exact w23_a3c
    have w24_a40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m24]; exact w23_a40
    have w24_a44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m24]; exact w23_a44
    have w24_1020 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m24]; exact w23_1020
    have w24_1024 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m24]; exact w23_1024
    clear w23_1024 w23_1020 w23_a44 w23_a40 w23_a3c w23_a38 w23_a34 w23_a30 w23_a2c w23_a28 w23_a24 w23_a20 w23_32c w23_328 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_19 g23_18 g23_11 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
    exact .inl ⟨(fun ⟨vp8', vl8', h0', te8', h1', h2', h3', _⟩ => by rw [hr8] at h0'; cases h0'; rw [ht8] at h1'; cases h1'; rw [hr19] at h3'; cases h3'), sv_fail F E24 s24 t24 (fun x hx => (fR24 x hx).trans (fM x hx).symm) V24 hret g24_2 g24_18 hO g24_3 g24_4⟩
  rotate_left
  · rw [hr19] at R19
    obtain ⟨a0_19, a1_19⟩ := R19
    have g19_10 : reg n19 a0 = BitVec.ofNat 32 0x0 := a0_19
    have g19_11 : reg n19 a1 = BitVec.ofNat 32 0x1 := by rw [a1_19]; rfl
    -- 0x5CC
    obtain ⟨n20, c20, u20⟩ := s19.block svX2n5cc E19.self svX2n5cc_end
      ⟨trivial, trivial⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have s20 : St n20.mem SV n20 0x5CE (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have rb20 : ∀ q, reg n20 q = (runBlock svX2n5cc (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
    have g20_8 : reg n20 (8 : Fin 32) = op := by
      rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
    have g20_9 : reg n20 (9 : Fin 32) = x9 := by
      rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
    have g20_11 : reg n20 a1 = BitVec.ofNat 32 0x1 := by
      rw [rb20, runBlock_reg _ _ _ a1 s19.zero (by decide), g19_11]
    have g20_18 : reg n20 (18 : Fin 32) = out := by
      rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by
      rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
    have g20_21 : reg n20 (21 : Fin 32) = x21 := by
      rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = L := by
      rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = p0 := by
      rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = x25 := by
      rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = x26 := by
      rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
    have g20_10 : reg n20 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb20]; simp +decide only [runBlock, BInstr.run, svX2n5cc, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_11, g19_18, g19_19, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m20]; exact w19_30
    have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m20]; exact w19_34
    have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m20]; exact w19_38
    have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m20]; exact w19_3c
    have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m20]; exact w19_40
    have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m20]; exact w19_48
    have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m20]; exact w19_4c
    have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
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
    have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m20]; exact w19_80
    have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m20]; exact w19_84
    have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m20]; exact w19_88
    have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m20]; exact w19_8c
    have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m20]; exact w19_90
    have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m20]; exact w19_94
    have w20_328 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m20]; exact w19_328
    have w20_32c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m20]; exact w19_32c
    have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m20]; exact w19_a20
    have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m20]; exact w19_a24
    have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m20]; exact w19_a28
    have w20_a2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m20]; exact w19_a2c
    have w20_a30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m20]; exact w19_a30
    have w20_a34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m20]; exact w19_a34
    have w20_a38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m20]; exact w19_a38
    have w20_a3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m20]; exact w19_a3c
    have w20_a40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m20]; exact w19_a40
    have w20_a44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m20]; exact w19_a44
    have w20_1020 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m20]; exact w19_1020
    have w20_1024 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m20]; exact w19_1024
    clear w19_1024 w19_1020 w19_a44 w19_a40 w19_a3c w19_a38 w19_a34 w19_a30 w19_a2c w19_a28 w19_a24 w19_a20 w19_32c w19_328 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_40 w19_3c w19_38 w19_34 w19_30 g19_2 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 V19 E19 fR19 t19 fr19 K19 rk19 sp19 s19 c19
    -- 0x5CE: sw
    obtain ⟨n21, d21, s21, fr21, K21, W21, rg21⟩ := sv_sw F E20 s20 sv_at_5ce (off' := 0x5D0) (c := 0x44)
      (by decide) (by rw [g20_2]; sv_addr) (by decide) (by decide)
    have t21 : Steps n0 n21 := t20.trans d21
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.keep K21 (by decide)
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rg21 sp, g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg21 (3 : Fin 32), g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg21 (4 : Fin 32), g20_4]
    have g21_8 : reg n21 (8 : Fin 32) = op := by rw [rg21 (8 : Fin 32), g20_8]
    have g21_9 : reg n21 (9 : Fin 32) = x9 := by rw [rg21 (9 : Fin 32), g20_9]
    have g21_10 : reg n21 a0 = BitVec.ofNat 32 0x0 := by rw [rg21 a0, g20_10]
    have g21_11 : reg n21 a1 = BitVec.ofNat 32 0x1 := by rw [rg21 a1, g20_11]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rg21 (18 : Fin 32), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rg21 (19 : Fin 32), g20_19]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [rg21 (21 : Fin 32), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = L := by rw [rg21 (22 : Fin 32), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg21 (23 : Fin 32), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = p0 := by rw [rg21 (24 : Fin 32), g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [rg21 (25 : Fin 32), g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [rg21 (26 : Fin 32), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg21 (27 : Fin 32), g20_27]
    have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K21.w32 (by decide) (by decide)).trans w20_30
    have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K21.w32 (by decide) (by decide)).trans w20_34
    have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := (K21.w32 (by decide) (by decide)).trans w20_38
    have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := (K21.w32 (by decide) (by decide)).trans w20_3c
    have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K21.w32 (by decide) (by decide)).trans w20_40
    have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K21.w32 (by decide) (by decide)).trans w20_48
    have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K21.w32 (by decide) (by decide)).trans w20_4c
    have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K21.w32 (by decide) (by decide)).trans w20_50
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
    have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K21.w32 (by decide) (by decide)).trans w20_80
    have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K21.w32 (by decide) (by decide)).trans w20_84
    have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K21.w32 (by decide) (by decide)).trans w20_88
    have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K21.w32 (by decide) (by decide)).trans w20_8c
    have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K21.w32 (by decide) (by decide)).trans w20_90
    have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K21.w32 (by decide) (by decide)).trans w20_94
    have w21_328 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := (K21.w32 (by decide) (by decide)).trans w20_328
    have w21_32c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := (K21.w32 (by decide) (by decide)).trans w20_32c
    have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K21.w32 (by decide) (by decide)).trans w20_a20
    have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K21.w32 (by decide) (by decide)).trans w20_a24
    have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K21.w32 (by decide) (by decide)).trans w20_a28
    have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K21.w32 (by decide) (by decide)).trans w20_a2c
    have w21_a30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K21.w32 (by decide) (by decide)).trans w20_a30
    have w21_a34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K21.w32 (by decide) (by decide)).trans w20_a34
    have w21_a38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K21.w32 (by decide) (by decide)).trans w20_a38
    have w21_a3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K21.w32 (by decide) (by decide)).trans w20_a3c
    have w21_a40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K21.w32 (by decide) (by decide)).trans w20_a40
    have w21_a44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K21.w32 (by decide) (by decide)).trans w20_a44
    have w21_1020 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := (K21.w32 (by decide) (by decide)).trans w20_1020
    have w21_1024 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := (K21.w32 (by decide) (by decide)).trans w20_1024
    have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [W21, g20_11]
    clear w20_1024 w20_1020 w20_a44 w20_a40 w20_a3c w20_a38 w20_a34 w20_a30 w20_a2c w20_a28 w20_a24 w20_a20 w20_32c w20_328 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_40 w20_3c w20_38 w20_34 w20_30 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_11 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20 g19_11 g19_10 a1_19 a0_19
    -- 0x5D0: branch, not taken
    obtain ⟨n22, d22, u22⟩ := s21.notTaken E21.self 0x5D4 sv_at_5d0
      (by decide) (by rw [g21_10, s21.zero]; decide)
    have s22 : St n22.mem SV n22 0x5D4 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = op := by rw [u22.regs, g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = x9 := by rw [u22.regs, g21_9]
    have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_10]
    have g22_11 : reg n22 a1 = BitVec.ofNat 32 0x1 := by rw [u22.regs, g21_11]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = L := by rw [u22.regs, g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = p0 := by rw [u22.regs, g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u22.regs, g21_27]
    have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m22]; exact w21_30
    have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m22]; exact w21_34
    have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m22]; exact w21_38
    have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m22]; exact w21_3c
    have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m22]; exact w21_40
    have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m22]; exact w21_44
    have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m22]; exact w21_48
    have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m22]; exact w21_4c
    have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m22]; exact w21_50
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
    have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m22]; exact w21_80
    have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m22]; exact w21_84
    have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m22]; exact w21_88
    have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m22]; exact w21_8c
    have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m22]; exact w21_90
    have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m22]; exact w21_94
    have w22_328 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m22]; exact w21_328
    have w22_32c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m22]; exact w21_32c
    have w22_a20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m22]; exact w21_a20
    have w22_a24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m22]; exact w21_a24
    have w22_a28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m22]; exact w21_a28
    have w22_a2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m22]; exact w21_a2c
    have w22_a30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m22]; exact w21_a30
    have w22_a34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m22]; exact w21_a34
    have w22_a38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m22]; exact w21_a38
    have w22_a3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m22]; exact w21_a3c
    have w22_a40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m22]; exact w21_a40
    have w22_a44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m22]; exact w21_a44
    have w22_1020 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m22]; exact w21_1020
    have w22_1024 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m22]; exact w21_1024
    clear w21_44 w21_1024 w21_1020 w21_a44 w21_a40 w21_a3c w21_a38 w21_a34 w21_a30 w21_a2c w21_a28 w21_a24 w21_a20 w21_32c w21_328 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_40 w21_3c w21_38 w21_34 w21_30 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_19 g21_18 g21_11 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 rg21 W21 K21 fr21 s21 d21
    -- 0x5D4: lw
    obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_5d4 (off' := 0x5D6) (by decide)
      (by rw [g22_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s23 : St n23.mem SV n23 0x5D6 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
    have t23 : Steps n0 n23 := t22.trans (.single d23)
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.same m23
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
    have g23_8 : reg n23 (8 : Fin 32) = op := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
    have g23_9 : reg n23 (9 : Fin 32) = x9 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
    have g23_11 : reg n23 a1 = BitVec.ofNat 32 0x1 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_11]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
    have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = L := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = p0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
    have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x1 := by
      rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g22_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w22_44]
    have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m23]; exact w22_30
    have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m23]; exact w22_34
    have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m23]; exact w22_38
    have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m23]; exact w22_3c
    have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m23]; exact w22_40
    have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m23]; exact w22_44
    have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m23]; exact w22_48
    have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m23]; exact w22_4c
    have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
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
    have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m23]; exact w22_80
    have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m23]; exact w22_84
    have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m23]; exact w22_88
    have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m23]; exact w22_8c
    have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m23]; exact w22_90
    have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m23]; exact w22_94
    have w23_328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m23]; exact w22_328
    have w23_32c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m23]; exact w22_32c
    have w23_a20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m23]; exact w22_a20
    have w23_a24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m23]; exact w22_a24
    have w23_a28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m23]; exact w22_a28
    have w23_a2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m23]; exact w22_a2c
    have w23_a30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m23]; exact w22_a30
    have w23_a34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m23]; exact w22_a34
    have w23_a38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m23]; exact w22_a38
    have w23_a3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m23]; exact w22_a3c
    have w23_a40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m23]; exact w22_a40
    have w23_a44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m23]; exact w22_a44
    have w23_1020 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m23]; exact w22_1020
    have w23_1024 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m23]; exact w22_1024
    clear w22_1024 w22_1020 w22_a44 w22_a40 w22_a3c w22_a38 w22_a34 w22_a30 w22_a2c w22_a28 w22_a24 w22_a20 w22_32c w22_328 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_19 g22_18 g22_11 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    -- 0x5D6
    obtain ⟨n24, c24, u24⟩ := s23.block svX2n5d6 E23.self svX2n5d6_end
      ⟨trivial, trivial, trivial⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have s24 : St n24.mem SV n24 0x5DA (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have rb24 : ∀ q, reg n24 q = (runBlock svX2n5d6 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
    have g24_8 : reg n24 (8 : Fin 32) = op := by
      rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
    have g24_9 : reg n24 (9 : Fin 32) = x9 := by
      rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
    have g24_18 : reg n24 (18 : Fin 32) = out := by
      rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by
      rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
    have g24_21 : reg n24 (21 : Fin 32) = x21 := by
      rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = L := by
      rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = p0 := by
      rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = x25 := by
      rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = x26 := by
      rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
    have g24_10 : reg n24 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb24]; simp +decide only [runBlock, BInstr.run, svX2n5d6, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_11, g23_18, g23_19, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g24_11 : reg n24 a1 = BitVec.ofNat 32 0x16 := by
      rw [rb24]; simp +decide only [runBlock, BInstr.run, svX2n5d6, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_11, g23_18, g23_19, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m24]; exact w23_30
    have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m24]; exact w23_34
    have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m24]; exact w23_38
    have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m24]; exact w23_3c
    have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m24]; exact w23_40
    have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m24]; exact w23_44
    have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m24]; exact w23_48
    have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m24]; exact w23_4c
    have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
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
    have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m24]; exact w23_80
    have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m24]; exact w23_84
    have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m24]; exact w23_88
    have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m24]; exact w23_8c
    have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m24]; exact w23_90
    have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m24]; exact w23_94
    have w24_328 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m24]; exact w23_328
    have w24_32c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m24]; exact w23_32c
    have w24_a20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m24]; exact w23_a20
    have w24_a24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m24]; exact w23_a24
    have w24_a28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m24]; exact w23_a28
    have w24_a2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m24]; exact w23_a2c
    have w24_a30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m24]; exact w23_a30
    have w24_a34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m24]; exact w23_a34
    have w24_a38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m24]; exact w23_a38
    have w24_a3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m24]; exact w23_a3c
    have w24_a40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m24]; exact w23_a40
    have w24_a44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m24]; exact w23_a44
    have w24_1020 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m24]; exact w23_1020
    have w24_1024 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m24]; exact w23_1024
    clear w23_1024 w23_1020 w23_a44 w23_a40 w23_a3c w23_a38 w23_a34 w23_a30 w23_a2c w23_a28 w23_a24 w23_a20 w23_32c w23_328 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 g23_10 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_19 g23_18 g23_11 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
    -- 0x5DA: sw
    obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_5da (off' := 0x5DC) (c := 0x44)
      (by decide) (by rw [g24_2]; sv_addr) (by decide) (by decide)
    have t25 : Steps n0 n25 := t24.trans d25
    have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
    have E25 : SvCode n25.mem := E24.fr F fr25
    have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
    have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
    have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
    have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
    have g25_8 : reg n25 (8 : Fin 32) = op := by rw [rg25 (8 : Fin 32), g24_8]
    have g25_9 : reg n25 (9 : Fin 32) = x9 := by rw [rg25 (9 : Fin 32), g24_9]
    have g25_10 : reg n25 a0 = BitVec.ofNat 32 0x1 := by rw [rg25 a0, g24_10]
    have g25_11 : reg n25 a1 = BitVec.ofNat 32 0x16 := by rw [rg25 a1, g24_11]
    have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
    have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
    have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rg25 (21 : Fin 32), g24_21]
    have g25_22 : reg n25 (22 : Fin 32) = L := by rw [rg25 (22 : Fin 32), g24_22]
    have g25_23 : reg n25 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg25 (23 : Fin 32), g24_23]
    have g25_24 : reg n25 (24 : Fin 32) = p0 := by rw [rg25 (24 : Fin 32), g24_24]
    have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rg25 (25 : Fin 32), g24_25]
    have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rg25 (26 : Fin 32), g24_26]
    have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg25 (27 : Fin 32), g24_27]
    have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K25.w32 (by decide) (by decide)).trans w24_30
    have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K25.w32 (by decide) (by decide)).trans w24_34
    have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := (K25.w32 (by decide) (by decide)).trans w24_38
    have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := (K25.w32 (by decide) (by decide)).trans w24_3c
    have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K25.w32 (by decide) (by decide)).trans w24_40
    have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K25.w32 (by decide) (by decide)).trans w24_48
    have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K25.w32 (by decide) (by decide)).trans w24_4c
    have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K25.w32 (by decide) (by decide)).trans w24_50
    have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K25.w32 (by decide) (by decide)).trans w24_54
    have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K25.w32 (by decide) (by decide)).trans w24_58
    have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K25.w32 (by decide) (by decide)).trans w24_5c
    have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K25.w32 (by decide) (by decide)).trans w24_60
    have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K25.w32 (by decide) (by decide)).trans w24_64
    have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K25.w32 (by decide) (by decide)).trans w24_68
    have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K25.w32 (by decide) (by decide)).trans w24_6c
    have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K25.w32 (by decide) (by decide)).trans w24_70
    have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K25.w32 (by decide) (by decide)).trans w24_74
    have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K25.w32 (by decide) (by decide)).trans w24_78
    have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K25.w32 (by decide) (by decide)).trans w24_7c
    have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K25.w32 (by decide) (by decide)).trans w24_80
    have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K25.w32 (by decide) (by decide)).trans w24_84
    have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K25.w32 (by decide) (by decide)).trans w24_88
    have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K25.w32 (by decide) (by decide)).trans w24_8c
    have w25_90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K25.w32 (by decide) (by decide)).trans w24_90
    have w25_94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K25.w32 (by decide) (by decide)).trans w24_94
    have w25_328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := (K25.w32 (by decide) (by decide)).trans w24_328
    have w25_32c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := (K25.w32 (by decide) (by decide)).trans w24_32c
    have w25_a20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K25.w32 (by decide) (by decide)).trans w24_a20
    have w25_a24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K25.w32 (by decide) (by decide)).trans w24_a24
    have w25_a28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K25.w32 (by decide) (by decide)).trans w24_a28
    have w25_a2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K25.w32 (by decide) (by decide)).trans w24_a2c
    have w25_a30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K25.w32 (by decide) (by decide)).trans w24_a30
    have w25_a34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K25.w32 (by decide) (by decide)).trans w24_a34
    have w25_a38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K25.w32 (by decide) (by decide)).trans w24_a38
    have w25_a3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K25.w32 (by decide) (by decide)).trans w24_a3c
    have w25_a40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K25.w32 (by decide) (by decide)).trans w24_a40
    have w25_a44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K25.w32 (by decide) (by decide)).trans w24_a44
    have w25_1020 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := (K25.w32 (by decide) (by decide)).trans w24_1020
    have w25_1024 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := (K25.w32 (by decide) (by decide)).trans w24_1024
    have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [W25, g24_11]
    clear w24_1024 w24_1020 w24_a44 w24_a40 w24_a3c w24_a38 w24_a34 w24_a30 w24_a2c w24_a28 w24_a24 w24_a20 w24_32c w24_328 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 g24_11 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
    -- 0x5DC: branch, taken
    obtain ⟨n26, d26, u26⟩ := s25.taken E25.self 0xB46 sv_at_5dc
      (by decide) (by rw [g25_10, s25.zero]; decide)
    have s26 : St n26.mem SV n26 0xB46 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans (.single d26)
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = op := by rw [u26.regs, g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = x9 := by rw [u26.regs, g25_9]
    have g26_10 : reg n26 a0 = BitVec.ofNat 32 0x1 := by rw [u26.regs, g25_10]
    have g26_11 : reg n26 a1 = BitVec.ofNat 32 0x16 := by rw [u26.regs, g25_11]
    have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, g25_19]
    have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = L := by rw [u26.regs, g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u26.regs, g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = p0 := by rw [u26.regs, g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, g25_27]
    have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m26]; exact w25_30
    have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m26]; exact w25_34
    have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m26]; exact w25_38
    have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m26]; exact w25_3c
    have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m26]; exact w25_40
    have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m26]; exact w25_44
    have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m26]; exact w25_48
    have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m26]; exact w25_4c
    have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m26]; exact w25_50
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
    have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m26]; exact w25_80
    have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m26]; exact w25_84
    have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m26]; exact w25_88
    have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m26]; exact w25_8c
    have w26_90 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m26]; exact w25_90
    have w26_94 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m26]; exact w25_94
    have w26_328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m26]; exact w25_328
    have w26_32c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m26]; exact w25_32c
    have w26_a20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m26]; exact w25_a20
    have w26_a24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m26]; exact w25_a24
    have w26_a28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m26]; exact w25_a28
    have w26_a2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m26]; exact w25_a2c
    have w26_a30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m26]; exact w25_a30
    have w26_a34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m26]; exact w25_a34
    have w26_a38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m26]; exact w25_a38
    have w26_a3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m26]; exact w25_a3c
    have w26_a40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m26]; exact w25_a40
    have w26_a44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m26]; exact w25_a44
    have w26_1020 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m26]; exact w25_1020
    have w26_1024 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m26]; exact w25_1024
    clear w25_44 w25_1024 w25_1020 w25_a44 w25_a40 w25_a3c w25_a38 w25_a34 w25_a30 w25_a2c w25_a28 w25_a24 w25_a20 w25_32c w25_328 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_40 w25_3c w25_38 w25_34 w25_30 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_19 g25_18 g25_11 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
    -- 0xB46: lw
    obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_b46 (off' := 0xB48) (by decide)
      (by rw [g26_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s27 : St n27.mem SV n27 0xB48 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = op := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = x9 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
    have g27_10 : reg n27 a0 = BitVec.ofNat 32 0x1 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_10]
    have g27_11 : reg n27 a1 = BitVec.ofNat 32 0x16 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_11]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
    have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = L := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = p0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
    have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m27]; exact w26_30
    have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m27]; exact w26_34
    have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m27]; exact w26_38
    have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m27]; exact w26_3c
    have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m27]; exact w26_40
    have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m27]; exact w26_44
    have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m27]; exact w26_48
    have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m27]; exact w26_4c
    have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m27]; exact w26_50
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
    have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m27]; exact w26_80
    have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m27]; exact w26_84
    have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m27]; exact w26_88
    have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m27]; exact w26_8c
    have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m27]; exact w26_90
    have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m27]; exact w26_94
    have w27_328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m27]; exact w26_328
    have w27_32c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m27]; exact w26_32c
    have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m27]; exact w26_a20
    have w27_a24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m27]; exact w26_a24
    have w27_a28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m27]; exact w26_a28
    have w27_a2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m27]; exact w26_a2c
    have w27_a30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m27]; exact w26_a30
    have w27_a34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m27]; exact w26_a34
    have w27_a38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m27]; exact w26_a38
    have w27_a3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m27]; exact w26_a3c
    have w27_a40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m27]; exact w26_a40
    have w27_a44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m27]; exact w26_a44
    have w27_1020 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m27]; exact w26_1020
    have w27_1024 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m27]; exact w26_1024
    clear w26_1024 w26_1020 w26_a44 w26_a40 w26_a3c w26_a38 w26_a34 w26_a30 w26_a2c w26_a28 w26_a24 w26_a20 w26_32c w26_328 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_19 g26_18 g26_11 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
    -- 0xB48: j
    obtain ⟨n28, d28, u28⟩ := s27.jump E27.self sv_at_b48 (off' := 0x966) (by decide)
      (by rw [s27.pc]; decide)
    have s28 : St n28.mem SV n28 0x966 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = op := by rw [u28.regs, g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = x9 := by rw [u28.regs, g27_9]
    have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x1 := by rw [u28.regs, g27_10]
    have g28_11 : reg n28 a1 = BitVec.ofNat 32 0x16 := by rw [u28.regs, g27_11]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
    have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = L := by rw [u28.regs, g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u28.regs, g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = p0 := by rw [u28.regs, g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, g27_27]
    have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m28]; exact w27_30
    have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m28]; exact w27_34
    have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m28]; exact w27_38
    have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m28]; exact w27_3c
    have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m28]; exact w27_40
    have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m28]; exact w27_44
    have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m28]; exact w27_48
    have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m28]; exact w27_4c
    have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m28]; exact w27_50
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
    have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m28]; exact w27_80
    have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m28]; exact w27_84
    have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m28]; exact w27_88
    have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m28]; exact w27_8c
    have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m28]; exact w27_90
    have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m28]; exact w27_94
    have w28_328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m28]; exact w27_328
    have w28_32c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m28]; exact w27_32c
    have w28_a20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m28]; exact w27_a20
    have w28_a24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m28]; exact w27_a24
    have w28_a28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m28]; exact w27_a28
    have w28_a2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m28]; exact w27_a2c
    have w28_a30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m28]; exact w27_a30
    have w28_a34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m28]; exact w27_a34
    have w28_a38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m28]; exact w27_a38
    have w28_a3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m28]; exact w27_a3c
    have w28_a40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m28]; exact w27_a40
    have w28_a44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m28]; exact w27_a44
    have w28_1020 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m28]; exact w27_1020
    have w28_1024 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m28]; exact w27_1024
    clear w27_1024 w27_1020 w27_a44 w27_a40 w27_a3c w27_a38 w27_a34 w27_a30 w27_a2c w27_a28 w27_a24 w27_a20 w27_32c w27_328 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_44 w27_40 w27_3c w27_38 w27_34 w27_30 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_19 g27_18 g27_11 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
    exact .inl ⟨(fun ⟨vp8', vl8', h0', te8', h1', h2', h3', _⟩ => by rw [hr8] at h0'; cases h0'; rw [ht8] at h1'; cases h1'; rw [hr19] at h3'; cases h3'), sv_fail F E28 s28 t28 (fun x hx => (fR28 x hx).trans (fM x hx).symm) V28 hret g28_2 g28_18 hO g28_3 g28_4⟩
  rw [hr19] at R19
  obtain ⟨a0_19, a1_19⟩ := R19
  have g19_10 : reg n19 a0 = BitVec.ofNat 32 0x0 := a0_19
  have g19_11 : reg n19 a1 = BitVec.ofNat 32 0x0 := by rw [a1_19]; rfl
  -- 0x5CC
  obtain ⟨n20, c20, u20⟩ := s19.block svX2n5cc E19.self svX2n5cc_end
    ⟨trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x5CE (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svX2n5cc (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = op := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = x9 := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_11 : reg n20 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb20, runBlock_reg _ _ _ a1 s19.zero (by decide), g19_11]
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = L := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = p0 := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_10 : reg n20 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svX2n5cc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_11, g19_18, g19_19, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m20]; exact w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m20]; exact w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m20]; exact w19_38
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m20]; exact w19_3c
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m20]; exact w19_40
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m20]; exact w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m20]; exact w19_4c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
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
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m20]; exact w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m20]; exact w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m20]; exact w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m20]; exact w19_8c
  have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m20]; exact w19_90
  have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m20]; exact w19_94
  have w20_328 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m20]; exact w19_328
  have w20_32c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m20]; exact w19_32c
  have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m20]; exact w19_a20
  have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m20]; exact w19_a24
  have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m20]; exact w19_a28
  have w20_a2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m20]; exact w19_a2c
  have w20_a30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m20]; exact w19_a30
  have w20_a34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m20]; exact w19_a34
  have w20_a38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m20]; exact w19_a38
  have w20_a3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m20]; exact w19_a3c
  have w20_a40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m20]; exact w19_a40
  have w20_a44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m20]; exact w19_a44
  have w20_1020 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m20]; exact w19_1020
  have w20_1024 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m20]; exact w19_1024
  clear w19_1024 w19_1020 w19_a44 w19_a40 w19_a3c w19_a38 w19_a34 w19_a30 w19_a2c w19_a28 w19_a24 w19_a20 w19_32c w19_328 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_40 w19_3c w19_38 w19_34 w19_30 g19_2 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 V19 E19 fR19 t19 fr19 K19 rk19 sp19 s19 c19
  -- 0x5CE: sw
  obtain ⟨n21, d21, s21, fr21, K21, W21, rg21⟩ := sv_sw F E20 s20 sv_at_5ce (off' := 0x5D0) (c := 0x44)
    (by decide) (by rw [g20_2]; sv_addr) (by decide) (by decide)
  have t21 : Steps n0 n21 := t20.trans d21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keep K21 (by decide)
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rg21 sp, g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg21 (3 : Fin 32), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg21 (4 : Fin 32), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = op := by rw [rg21 (8 : Fin 32), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = x9 := by rw [rg21 (9 : Fin 32), g20_9]
  have g21_10 : reg n21 a0 = BitVec.ofNat 32 0x0 := by rw [rg21 a0, g20_10]
  have g21_11 : reg n21 a1 = BitVec.ofNat 32 0x0 := by rw [rg21 a1, g20_11]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rg21 (18 : Fin 32), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rg21 (19 : Fin 32), g20_19]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [rg21 (21 : Fin 32), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = L := by rw [rg21 (22 : Fin 32), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg21 (23 : Fin 32), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = p0 := by rw [rg21 (24 : Fin 32), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [rg21 (25 : Fin 32), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [rg21 (26 : Fin 32), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg21 (27 : Fin 32), g20_27]
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K21.w32 (by decide) (by decide)).trans w20_30
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K21.w32 (by decide) (by decide)).trans w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := (K21.w32 (by decide) (by decide)).trans w20_38
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := (K21.w32 (by decide) (by decide)).trans w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K21.w32 (by decide) (by decide)).trans w20_40
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K21.w32 (by decide) (by decide)).trans w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K21.w32 (by decide) (by decide)).trans w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K21.w32 (by decide) (by decide)).trans w20_50
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
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K21.w32 (by decide) (by decide)).trans w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K21.w32 (by decide) (by decide)).trans w20_84
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K21.w32 (by decide) (by decide)).trans w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K21.w32 (by decide) (by decide)).trans w20_8c
  have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K21.w32 (by decide) (by decide)).trans w20_90
  have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K21.w32 (by decide) (by decide)).trans w20_94
  have w21_328 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := (K21.w32 (by decide) (by decide)).trans w20_328
  have w21_32c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := (K21.w32 (by decide) (by decide)).trans w20_32c
  have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K21.w32 (by decide) (by decide)).trans w20_a20
  have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K21.w32 (by decide) (by decide)).trans w20_a24
  have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K21.w32 (by decide) (by decide)).trans w20_a28
  have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K21.w32 (by decide) (by decide)).trans w20_a2c
  have w21_a30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K21.w32 (by decide) (by decide)).trans w20_a30
  have w21_a34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K21.w32 (by decide) (by decide)).trans w20_a34
  have w21_a38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K21.w32 (by decide) (by decide)).trans w20_a38
  have w21_a3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K21.w32 (by decide) (by decide)).trans w20_a3c
  have w21_a40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K21.w32 (by decide) (by decide)).trans w20_a40
  have w21_a44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K21.w32 (by decide) (by decide)).trans w20_a44
  have w21_1020 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := (K21.w32 (by decide) (by decide)).trans w20_1020
  have w21_1024 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := (K21.w32 (by decide) (by decide)).trans w20_1024
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x0 := by rw [W21, g20_11]
  clear w20_1024 w20_1020 w20_a44 w20_a40 w20_a3c w20_a38 w20_a34 w20_a30 w20_a2c w20_a28 w20_a24 w20_a20 w20_32c w20_328 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_40 w20_3c w20_38 w20_34 w20_30 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_11 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20 g19_11 g19_10 a1_19 a0_19
  -- 0x5D0: branch, not taken
  obtain ⟨n22, d22, u22⟩ := s21.notTaken E21.self 0x5D4 sv_at_5d0
    (by decide) (by rw [g21_10, s21.zero]; decide)
  have s22 : St n22.mem SV n22 0x5D4 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = op := by rw [u22.regs, g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = x9 := by rw [u22.regs, g21_9]
  have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_10]
  have g22_11 : reg n22 a1 = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_11]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = L := by rw [u22.regs, g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = p0 := by rw [u22.regs, g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u22.regs, g21_27]
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m22]; exact w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m22]; exact w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m22]; exact w21_38
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m22]; exact w21_3c
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m22]; exact w21_40
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x0 := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m22]; exact w21_48
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m22]; exact w21_4c
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m22]; exact w21_50
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
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m22]; exact w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m22]; exact w21_84
  have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m22]; exact w21_88
  have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m22]; exact w21_8c
  have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m22]; exact w21_90
  have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m22]; exact w21_94
  have w22_328 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m22]; exact w21_328
  have w22_32c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m22]; exact w21_32c
  have w22_a20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m22]; exact w21_a20
  have w22_a24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m22]; exact w21_a24
  have w22_a28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m22]; exact w21_a28
  have w22_a2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m22]; exact w21_a2c
  have w22_a30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m22]; exact w21_a30
  have w22_a34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m22]; exact w21_a34
  have w22_a38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m22]; exact w21_a38
  have w22_a3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m22]; exact w21_a3c
  have w22_a40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m22]; exact w21_a40
  have w22_a44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m22]; exact w21_a44
  have w22_1020 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m22]; exact w21_1020
  have w22_1024 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m22]; exact w21_1024
  clear w21_44 w21_1024 w21_1020 w21_a44 w21_a40 w21_a3c w21_a38 w21_a34 w21_a30 w21_a2c w21_a28 w21_a24 w21_a20 w21_32c w21_328 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_40 w21_3c w21_38 w21_34 w21_30 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_19 g21_18 g21_11 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 rg21 W21 K21 fr21 s21 d21
  -- 0x5D4: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_5d4 (off' := 0x5D6) (by decide)
    (by rw [g22_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s23 : St n23.mem SV n23 0x5D6 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = op := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = x9 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_11 : reg n23 a1 = BitVec.ofNat 32 0x0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_11]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = L := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = p0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x0 := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w22_44]
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m23]; exact w22_38
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m23]; exact w22_3c
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m23]; exact w22_40
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x0 := by rw [m23]; exact w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m23]; exact w22_48
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m23]; exact w22_4c
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
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
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m23]; exact w22_84
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m23]; exact w22_88
  have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m23]; exact w22_8c
  have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m23]; exact w22_90
  have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m23]; exact w22_94
  have w23_328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m23]; exact w22_328
  have w23_32c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m23]; exact w22_32c
  have w23_a20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m23]; exact w22_a20
  have w23_a24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m23]; exact w22_a24
  have w23_a28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m23]; exact w22_a28
  have w23_a2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m23]; exact w22_a2c
  have w23_a30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m23]; exact w22_a30
  have w23_a34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m23]; exact w22_a34
  have w23_a38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m23]; exact w22_a38
  have w23_a3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m23]; exact w22_a3c
  have w23_a40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m23]; exact w22_a40
  have w23_a44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m23]; exact w22_a44
  have w23_1020 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m23]; exact w22_1020
  have w23_1024 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m23]; exact w22_1024
  clear w22_1024 w22_1020 w22_a44 w22_a40 w22_a3c w22_a38 w22_a34 w22_a30 w22_a2c w22_a28 w22_a24 w22_a20 w22_32c w22_328 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_19 g22_18 g22_11 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0x5D6
  obtain ⟨n24, c24, u24⟩ := s23.block svX2n5d6 E23.self svX2n5d6_end
    ⟨trivial, trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem SV n24 0x5DA (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock svX2n5d6 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
  have g24_8 : reg n24 (8 : Fin 32) = op := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = x9 := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = out := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by
    rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = L := by
    rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = p0 := by
    rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by
    rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_10 : reg n24 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svX2n5d6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_11, g23_18, g23_19, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g24_11 : reg n24 a1 = BitVec.ofNat 32 0x16 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svX2n5d6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_11, g23_18, g23_19, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m24]; exact w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m24]; exact w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m24]; exact w23_38
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m24]; exact w23_3c
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m24]; exact w23_40
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x0 := by rw [m24]; exact w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m24]; exact w23_48
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m24]; exact w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
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
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m24]; exact w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m24]; exact w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m24]; exact w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m24]; exact w23_8c
  have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m24]; exact w23_90
  have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m24]; exact w23_94
  have w24_328 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m24]; exact w23_328
  have w24_32c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m24]; exact w23_32c
  have w24_a20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m24]; exact w23_a20
  have w24_a24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m24]; exact w23_a24
  have w24_a28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m24]; exact w23_a28
  have w24_a2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m24]; exact w23_a2c
  have w24_a30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m24]; exact w23_a30
  have w24_a34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m24]; exact w23_a34
  have w24_a38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m24]; exact w23_a38
  have w24_a3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m24]; exact w23_a3c
  have w24_a40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m24]; exact w23_a40
  have w24_a44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m24]; exact w23_a44
  have w24_1020 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m24]; exact w23_1020
  have w24_1024 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m24]; exact w23_1024
  clear w23_1024 w23_1020 w23_a44 w23_a40 w23_a3c w23_a38 w23_a34 w23_a30 w23_a2c w23_a28 w23_a24 w23_a20 w23_32c w23_328 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 g23_10 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_19 g23_18 g23_11 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0x5DA: sw
  obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_5da (off' := 0x5DC) (c := 0x44)
    (by decide) (by rw [g24_2]; sv_addr) (by decide) (by decide)
  have t25 : Steps n0 n25 := t24.trans d25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = op := by rw [rg25 (8 : Fin 32), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = x9 := by rw [rg25 (9 : Fin 32), g24_9]
  have g25_10 : reg n25 a0 = BitVec.ofNat 32 0x0 := by rw [rg25 a0, g24_10]
  have g25_11 : reg n25 a1 = BitVec.ofNat 32 0x16 := by rw [rg25 a1, g24_11]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rg25 (21 : Fin 32), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = L := by rw [rg25 (22 : Fin 32), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg25 (23 : Fin 32), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = p0 := by rw [rg25 (24 : Fin 32), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rg25 (25 : Fin 32), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rg25 (26 : Fin 32), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg25 (27 : Fin 32), g24_27]
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K25.w32 (by decide) (by decide)).trans w24_30
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K25.w32 (by decide) (by decide)).trans w24_34
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := (K25.w32 (by decide) (by decide)).trans w24_38
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := (K25.w32 (by decide) (by decide)).trans w24_3c
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K25.w32 (by decide) (by decide)).trans w24_40
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K25.w32 (by decide) (by decide)).trans w24_48
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K25.w32 (by decide) (by decide)).trans w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K25.w32 (by decide) (by decide)).trans w24_50
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K25.w32 (by decide) (by decide)).trans w24_54
  have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K25.w32 (by decide) (by decide)).trans w24_58
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K25.w32 (by decide) (by decide)).trans w24_5c
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K25.w32 (by decide) (by decide)).trans w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K25.w32 (by decide) (by decide)).trans w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K25.w32 (by decide) (by decide)).trans w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K25.w32 (by decide) (by decide)).trans w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K25.w32 (by decide) (by decide)).trans w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K25.w32 (by decide) (by decide)).trans w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K25.w32 (by decide) (by decide)).trans w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K25.w32 (by decide) (by decide)).trans w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K25.w32 (by decide) (by decide)).trans w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K25.w32 (by decide) (by decide)).trans w24_84
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K25.w32 (by decide) (by decide)).trans w24_88
  have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K25.w32 (by decide) (by decide)).trans w24_8c
  have w25_90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K25.w32 (by decide) (by decide)).trans w24_90
  have w25_94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K25.w32 (by decide) (by decide)).trans w24_94
  have w25_328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := (K25.w32 (by decide) (by decide)).trans w24_328
  have w25_32c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := (K25.w32 (by decide) (by decide)).trans w24_32c
  have w25_a20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K25.w32 (by decide) (by decide)).trans w24_a20
  have w25_a24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K25.w32 (by decide) (by decide)).trans w24_a24
  have w25_a28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K25.w32 (by decide) (by decide)).trans w24_a28
  have w25_a2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K25.w32 (by decide) (by decide)).trans w24_a2c
  have w25_a30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K25.w32 (by decide) (by decide)).trans w24_a30
  have w25_a34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K25.w32 (by decide) (by decide)).trans w24_a34
  have w25_a38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K25.w32 (by decide) (by decide)).trans w24_a38
  have w25_a3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K25.w32 (by decide) (by decide)).trans w24_a3c
  have w25_a40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K25.w32 (by decide) (by decide)).trans w24_a40
  have w25_a44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K25.w32 (by decide) (by decide)).trans w24_a44
  have w25_1020 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := (K25.w32 (by decide) (by decide)).trans w24_1020
  have w25_1024 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := (K25.w32 (by decide) (by decide)).trans w24_1024
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [W25, g24_11]
  clear w24_1024 w24_1020 w24_a44 w24_a40 w24_a3c w24_a38 w24_a34 w24_a30 w24_a2c w24_a28 w24_a24 w24_a20 w24_32c w24_328 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 g24_11 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0x5DC: branch, not taken
  obtain ⟨n26, d26, u26⟩ := s25.notTaken E25.self 0x5E0 sv_at_5dc
    (by decide) (by rw [g25_10, s25.zero]; decide)
  have s26 : St n26.mem SV n26 0x5E0 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = op := by rw [u26.regs, g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = x9 := by rw [u26.regs, g25_9]
  have g26_10 : reg n26 a0 = BitVec.ofNat 32 0x0 := by rw [u26.regs, g25_10]
  have g26_11 : reg n26 a1 = BitVec.ofNat 32 0x16 := by rw [u26.regs, g25_11]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, g25_19]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = L := by rw [u26.regs, g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u26.regs, g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = p0 := by rw [u26.regs, g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, g25_27]
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m26]; exact w25_30
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m26]; exact w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m26]; exact w25_38
  have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m26]; exact w25_3c
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m26]; exact w25_40
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m26]; exact w25_44
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m26]; exact w25_48
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m26]; exact w25_4c
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m26]; exact w25_50
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
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m26]; exact w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m26]; exact w25_84
  have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m26]; exact w25_88
  have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m26]; exact w25_8c
  have w26_90 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m26]; exact w25_90
  have w26_94 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m26]; exact w25_94
  have w26_328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m26]; exact w25_328
  have w26_32c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m26]; exact w25_32c
  have w26_a20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m26]; exact w25_a20
  have w26_a24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m26]; exact w25_a24
  have w26_a28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m26]; exact w25_a28
  have w26_a2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m26]; exact w25_a2c
  have w26_a30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m26]; exact w25_a30
  have w26_a34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m26]; exact w25_a34
  have w26_a38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m26]; exact w25_a38
  have w26_a3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m26]; exact w25_a3c
  have w26_a40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m26]; exact w25_a40
  have w26_a44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m26]; exact w25_a44
  have w26_1020 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m26]; exact w25_1020
  have w26_1024 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m26]; exact w25_1024
  clear w25_44 w25_1024 w25_1020 w25_a44 w25_a40 w25_a3c w25_a38 w25_a34 w25_a30 w25_a2c w25_a28 w25_a24 w25_a20 w25_32c w25_328 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_40 w25_3c w25_38 w25_34 w25_30 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_19 g25_18 g25_11 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
  -- 0x5E0: branch, taken
  obtain ⟨n27, d27, u27⟩ := s26.taken E26.self 0x60E sv_at_5e0
    (by decide) (by rw [g26_23, s26.zero]; rfl)
  have s27 : St n27.mem SV n27 0x60E (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = op := by rw [u27.regs, g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = x9 := by rw [u27.regs, g26_9]
  have g27_10 : reg n27 a0 = BitVec.ofNat 32 0x0 := by rw [u27.regs, g26_10]
  have g27_11 : reg n27 a1 = BitVec.ofNat 32 0x16 := by rw [u27.regs, g26_11]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, g26_19]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = L := by rw [u27.regs, g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u27.regs, g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = p0 := by rw [u27.regs, g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u27.regs, g26_27]
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m27]; exact w26_30
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m27]; exact w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl8 := by rw [m27]; exact w26_38
  have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp8 := by rw [m27]; exact w26_3c
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m27]; exact w26_40
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m27]; exact w26_44
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m27]; exact w26_48
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m27]; exact w26_4c
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m27]; exact w26_50
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
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m27]; exact w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m27]; exact w26_84
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m27]; exact w26_88
  have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m27]; exact w26_8c
  have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m27]; exact w26_90
  have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m27]; exact w26_94
  have w27_328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (rp2) + BitVec.ofNat 32 (te8.header + te8.len) := by rw [m27]; exact w26_328
  have w27_32c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (rem2) - BitVec.ofNat 32 (te8.header + te8.len) := by rw [m27]; exact w26_32c
  have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m27]; exact w26_a20
  have w27_a24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m27]; exact w26_a24
  have w27_a28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m27]; exact w26_a28
  have w27_a2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m27]; exact w26_a2c
  have w27_a30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m27]; exact w26_a30
  have w27_a34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m27]; exact w26_a34
  have w27_a38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m27]; exact w26_a38
  have w27_a3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m27]; exact w26_a3c
  have w27_a40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m27]; exact w26_a40
  have w27_a44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m27]; exact w26_a44
  have w27_1020 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = vp8 := by rw [m27]; exact w26_1020
  have w27_1024 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = vl8 := by rw [m27]; exact w26_1024
  clear w26_1024 w26_1020 w26_a44 w26_a40 w26_a3c w26_a38 w26_a34 w26_a30 w26_a2c w26_a28 w26_a24 w26_a20 w26_32c w26_328 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_19 g26_18 g26_11 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  exact .inr ⟨vp8, vl8, hr8, te8, ht8, hz_12, hr19, n27, t27, s27, E27, V27, fR27, g27_2, g27_3, g27_4, g27_8, g27_9, g27_18, g27_19, g27_21, g27_25, g27_26, g27_27, w27_30, w27_34, w27_38, w27_3c, w27_40, w27_48, w27_4c, w27_50, w27_54, w27_58, w27_5c, w27_60, w27_64, w27_68, w27_6c, w27_70, w27_74, w27_78, w27_7c, w27_80, w27_84, w27_88, w27_8c, w27_90, w27_94, w27_a20, w27_a24, w27_a28, w27_a2c, w27_a30, w27_a34, w27_a38, w27_a3c, w27_a40, w27_a44⟩

end C3.RV32.Sv
