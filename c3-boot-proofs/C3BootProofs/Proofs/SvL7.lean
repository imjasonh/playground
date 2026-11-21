import C3BootProofs.Proofs.SvEcdsa

/-!
# `sigstore::verify`: the policy and the leaf's signature

From the extensions loop's end at 0x4EA to 0xA44: all five identity-policy slots are filled, `KeyUsage` and `ExtKeyUsage` were seen, the outer signature algorithm matches the tbsCertificate's, and the signature value is an ECDSA signature with 48-byte `r` and `s`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL7b32 : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0x16]
theorem svL7b32_end : blockEnd sigstoreVerifyCode 0xB32 svL7b32 = some 0xB34 := by
  simp only [svL7b32]
  rw [blockEnd, sv_at_b32]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL79ee : List BInstr :=
  [.alu .sltu a0 x0 a0]
theorem svL79ee_end : blockEnd sigstoreVerifyCode 0x9EE svL79ee = some 0x9F2 := by
  simp only [svL79ee]
  rw [blockEnd, sv_at_9ee]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL79f6 : List BInstr :=
  [.alu .and a1 a1 a2]
theorem svL79f6_end : blockEnd sigstoreVerifyCode 0x9F6 svL79f6 = some 0x9F8 := by
  simp only [svL79f6]
  rw [blockEnd, sv_at_9f6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL79f8 : List BInstr :=
  [.alu .and a0 a0 a1]
theorem svL79f8_end : blockEnd sigstoreVerifyCode 0x9F8 svL79f8 = some 0x9FA := by
  simp only [svL79f8]
  rw [blockEnd, sv_at_9f8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL79fe : List BInstr :=
  [.alu .add a1 x0 (27 : Fin 32)]
theorem svL79fe_end : blockEnd sigstoreVerifyCode 0x9FE svL79fe = some 0xA00 := by
  simp only [svL79fe]
  rw [blockEnd, sv_at_9fe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL7a26 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221]
theorem svL7a26_end : blockEnd sigstoreVerifyCode 0xA26 svL7a26 = some 0xA2E := by
  simp only [svL7a26]
  rw [blockEnd, sv_at_a26]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a2a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_l7 {B out bp x9 x21 x25 x26 f30 f34 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 orp arp sgp : Word} {orl arl sgl : Nat} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x4EA (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = x9)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
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
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem)
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
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl)
    (hrem : rem = 0)
    (or_in : SvIn B orp orl)
    (ar_in : SvIn B arp arl)
    (sg_in : SvIn B sgp sgl) :
    (¬ ((sl0 ≠ 0) ∧ (sl2 ≠ 0) ∧ (sl4 ≠ 0) ∧ (sl6 ≠ 0) ∧ ((if BitVec.ult 0 (sl8) then (1 : Word) else 0) &&& ((f30) &&& (f34)) ≠ 0) ∧ (memBytes M0 orp orl = memBytes M0 arp arl) ∧ ∃ sr43 ss43, ecdsaSigOf 48 M0 (sgp) (sgl) = .ok (sr43, ss43) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((sl0 ≠ 0) ∧
    (sl2 ≠ 0) ∧
    (sl4 ≠ 0) ∧
    (sl6 ≠ 0) ∧
    ((if BitVec.ult 0 (sl8) then (1 : Word) else 0) &&& ((f30) &&& (f34)) ≠ 0) ∧
    (memBytes M0 orp orl = memBytes M0 arp arl) ∧
    ∃ sr43 ss43, ecdsaSigOf 48 M0 (sgp) (sgl) = .ok (sr43, ss43) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xA44 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = x9 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 ((sr43).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 ((ss43).getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x4EA: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_4ea (off' := 0x4EC) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0x4EC (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_9 : reg n1 (9 : Fin 32) = x9 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, upd_ne (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_21]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_10 : reg n1 a0 = rem := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr, w0_40]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m1]; exact w0_30
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m1]; exact w0_34
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m1]; exact w0_40
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m1]; exact w0_4c
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  have w1_54 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m1]; exact w0_54
  have w1_58 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m1]; exact w0_58
  have w1_5c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m1]; exact w0_5c
  have w1_60 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m1]; exact w0_60
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m1]; exact w0_64
  have w1_68 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m1]; exact w0_68
  have w1_6c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m1]; exact w0_6c
  have w1_70 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m1]; exact w0_70
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m1]; exact w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m1]; exact w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m1]; exact w0_7c
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m1]; exact w0_80
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m1]; exact w0_84
  have w1_88 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m1]; exact w0_88
  have w1_8c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m1]; exact w0_8c
  have w1_90 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m1]; exact w0_90
  have w1_94 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m1]; exact w0_94
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
  -- 0x4EC: branch, taken
  obtain ⟨n2, d2, u2⟩ := s1.taken E1.self 0x9C0 sv_at_4ec
    (by decide) (by rw [g1_10, s1.zero]; exact br_beq_t hrem)
  have s2 : St n2.mem SV n2 0x9C0 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, g1_4]
  have g2_9 : reg n2 (9 : Fin 32) = x9 := by rw [u2.regs, g1_9]
  have g2_10 : reg n2 a0 = rem := by rw [u2.regs, g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, g1_21]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [u2.regs, g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m2]; exact w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m2]; exact w1_34
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m2]; exact w1_40
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m2]; exact w1_4c
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m2]; exact w1_54
  have w2_58 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m2]; exact w1_58
  have w2_5c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m2]; exact w1_5c
  have w2_60 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m2]; exact w1_60
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m2]; exact w1_64
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m2]; exact w1_68
  have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m2]; exact w1_6c
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m2]; exact w1_70
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m2]; exact w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m2]; exact w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m2]; exact w1_7c
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m2]; exact w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m2]; exact w1_84
  have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m2]; exact w1_88
  have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m2]; exact w1_8c
  have w2_90 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m2]; exact w1_90
  have w2_94 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m2]; exact w1_94
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
  clear w1_a44 w1_a40 w1_a3c w1_a38 w1_a34 w1_a30 w1_a2c w1_a28 w1_a24 w1_a20 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_40 w1_34 w1_30 g1_10 g1_27 g1_26 g1_25 g1_21 g1_19 g1_18 g1_9 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x9C0: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_9c0 (off' := 0x9C4) (by decide)
    (by rw [g2_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x9C4 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_9 : reg n3 (9 : Fin 32) = x9 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_10 : reg n3 a0 = sl0 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w2_a20]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m3]; exact w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m3]; exact w2_34
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m3]; exact w2_40
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m3]; exact w2_4c
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  have w3_54 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m3]; exact w2_54
  have w3_58 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m3]; exact w2_58
  have w3_5c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m3]; exact w2_5c
  have w3_60 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m3]; exact w2_60
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m3]; exact w2_64
  have w3_68 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m3]; exact w2_68
  have w3_6c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m3]; exact w2_6c
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m3]; exact w2_70
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m3]; exact w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m3]; exact w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m3]; exact w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m3]; exact w2_84
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m3]; exact w2_88
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m3]; exact w2_8c
  have w3_90 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m3]; exact w2_90
  have w3_94 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m3]; exact w2_94
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
  clear w2_a44 w2_a40 w2_a3c w2_a38 w2_a34 w2_a30 w2_a2c w2_a28 w2_a24 w2_a20 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_74 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_40 w2_34 w2_30 g2_27 g2_26 g2_25 g2_21 g2_19 g2_18 g2_10 g2_9 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x9C4: sw
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := sv_sw F E3 s3 sv_at_9c4 (off' := 0x9C6) (c := 0x48)
    (by decide) (by rw [g3_2]; sv_addr) (by decide) (by decide)
  have t4 : Steps n0 n4 := t3.trans d4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rg4 sp, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg4 (3 : Fin 32), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg4 (4 : Fin 32), g3_4]
  have g4_9 : reg n4 (9 : Fin 32) = x9 := by rw [rg4 (9 : Fin 32), g3_9]
  have g4_10 : reg n4 a0 = sl0 := by rw [rg4 a0, g3_10]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rg4 (18 : Fin 32), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rg4 (19 : Fin 32), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [rg4 (21 : Fin 32), g3_21]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [rg4 (25 : Fin 32), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [rg4 (26 : Fin 32), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg4 (27 : Fin 32), g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x48, 0x4)] := keep_kk3.trans K4.toL
  clear keep_kk3
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K4.w32 (by decide) (by decide)).trans w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K4.w32 (by decide) (by decide)).trans w3_34
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K4.w32 (by decide) (by decide)).trans w3_40
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K4.w32 (by decide) (by decide)).trans w3_4c
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K4.w32 (by decide) (by decide)).trans w3_50
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K4.w32 (by decide) (by decide)).trans w3_54
  have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K4.w32 (by decide) (by decide)).trans w3_58
  have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K4.w32 (by decide) (by decide)).trans w3_5c
  have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K4.w32 (by decide) (by decide)).trans w3_60
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K4.w32 (by decide) (by decide)).trans w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K4.w32 (by decide) (by decide)).trans w3_68
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K4.w32 (by decide) (by decide)).trans w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K4.w32 (by decide) (by decide)).trans w3_70
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K4.w32 (by decide) (by decide)).trans w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K4.w32 (by decide) (by decide)).trans w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K4.w32 (by decide) (by decide)).trans w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K4.w32 (by decide) (by decide)).trans w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K4.w32 (by decide) (by decide)).trans w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K4.w32 (by decide) (by decide)).trans w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K4.w32 (by decide) (by decide)).trans w3_8c
  have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K4.w32 (by decide) (by decide)).trans w3_90
  have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K4.w32 (by decide) (by decide)).trans w3_94
  have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K4.w32 (by decide) (by decide)).trans w3_a20
  have w4_a24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K4.w32 (by decide) (by decide)).trans w3_a24
  have w4_a28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K4.w32 (by decide) (by decide)).trans w3_a28
  have w4_a2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K4.w32 (by decide) (by decide)).trans w3_a2c
  have w4_a30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K4.w32 (by decide) (by decide)).trans w3_a30
  have w4_a34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K4.w32 (by decide) (by decide)).trans w3_a34
  have w4_a38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K4.w32 (by decide) (by decide)).trans w3_a38
  have w4_a3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K4.w32 (by decide) (by decide)).trans w3_a3c
  have w4_a40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K4.w32 (by decide) (by decide)).trans w3_a40
  have w4_a44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K4.w32 (by decide) (by decide)).trans w3_a44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [W4, g3_10]
  clear w3_a44 w3_a40 w3_a3c w3_a38 w3_a34 w3_a30 w3_a2c w3_a28 w3_a24 w3_a20 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_40 w3_34 w3_30 g3_10 g3_27 g3_26 g3_25 g3_21 g3_19 g3_18 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  by_cases hz_4 : sl0 ≠ 0
  rotate_left
  · -- 0x9C6: branch, taken
    obtain ⟨n5, d5, u5⟩ := s4.taken E4.self 0xB32 sv_at_9c6
      (by decide) (by rw [g4_10, s4.zero]; exact br_beq_t (Decidable.of_not_not hz_4))
    have s5 : St n5.mem SV n5 0xB32 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
    have g5_9 : reg n5 (9 : Fin 32) = x9 := by rw [u5.regs, g4_9]
    have g5_10 : reg n5 a0 = sl0 := by rw [u5.regs, g4_10]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
    have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
    have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, g4_27]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x48, 0x4)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m5]; exact w4_30
    have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m5]; exact w4_34
    have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m5]; exact w4_40
    have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m5]; exact w4_48
    have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m5]; exact w4_4c
    have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
    have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m5]; exact w4_54
    have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m5]; exact w4_58
    have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m5]; exact w4_5c
    have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m5]; exact w4_60
    have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m5]; exact w4_64
    have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m5]; exact w4_68
    have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m5]; exact w4_6c
    have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m5]; exact w4_70
    have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m5]; exact w4_74
    have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m5]; exact w4_78
    have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m5]; exact w4_7c
    have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m5]; exact w4_80
    have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m5]; exact w4_84
    have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m5]; exact w4_88
    have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m5]; exact w4_8c
    have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m5]; exact w4_90
    have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m5]; exact w4_94
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
    clear w4_48 w4_a44 w4_a40 w4_a3c w4_a38 w4_a34 w4_a30 w4_a2c w4_a28 w4_a24 w4_a20 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_40 w4_34 w4_30 g4_27 g4_26 g4_25 g4_21 g4_19 g4_18 g4_10 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 rg4 W4 K4 fr4 s4 d4
    -- 0xB32
    obtain ⟨n6, c6, u6⟩ := s5.block svL7b32 E5.self svL7b32_end
      ⟨trivial, trivial⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have s6 : St n6.mem SV n6 0xB34 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have rb6 : ∀ q, reg n6 q = (runBlock svL7b32 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
    have g6_9 : reg n6 (9 : Fin 32) = x9 := by
      rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
    have g6_10 : reg n6 a0 = sl0 := by
      rw [rb6, runBlock_reg _ _ _ a0 s5.zero (by decide), g5_10]
    have g6_18 : reg n6 (18 : Fin 32) = out := by
      rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = bp := by
      rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
    have g6_21 : reg n6 (21 : Fin 32) = x21 := by
      rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
    have g6_25 : reg n6 (25 : Fin 32) = x25 := by
      rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
    have g6_26 : reg n6 (26 : Fin 32) = x26 := by
      rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
    have g6_20 : reg n6 (20 : Fin 32) = BitVec.ofNat 32 0x16 := by
      rw [rb6]; simp +decide only [runBlock, BInstr.run, svL7b32, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g5_2, g5_3, g5_4, g5_9, g5_10, g5_18, g5_19, g5_21, g5_25, g5_26, g5_27, s5.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x48, 0x4)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m6]; exact w5_30
    have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m6]; exact w5_34
    have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m6]; exact w5_40
    have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m6]; exact w5_48
    have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m6]; exact w5_4c
    have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
    have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m6]; exact w5_54
    have w6_58 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m6]; exact w5_58
    have w6_5c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m6]; exact w5_5c
    have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m6]; exact w5_60
    have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m6]; exact w5_64
    have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m6]; exact w5_68
    have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m6]; exact w5_6c
    have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m6]; exact w5_70
    have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m6]; exact w5_74
    have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m6]; exact w5_78
    have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m6]; exact w5_7c
    have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m6]; exact w5_80
    have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m6]; exact w5_84
    have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m6]; exact w5_88
    have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m6]; exact w5_8c
    have w6_90 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m6]; exact w5_90
    have w6_94 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m6]; exact w5_94
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
    clear w5_a44 w5_a40 w5_a3c w5_a38 w5_a34 w5_a30 w5_a2c w5_a28 w5_a24 w5_a20 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_40 w5_34 w5_30 g5_27 g5_26 g5_25 g5_21 g5_19 g5_18 g5_10 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    -- 0xB34: j
    obtain ⟨n7, d7, u7⟩ := s6.jump E6.self sv_at_b34 (off' := 0x966) (by decide)
      (by rw [s6.pc]; decide)
    have s7 : St n7.mem SV n7 0x966 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
    have g7_9 : reg n7 (9 : Fin 32) = x9 := by rw [u7.regs, g6_9]
    have g7_10 : reg n7 a0 = sl0 := by rw [u7.regs, g6_10]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = BitVec.ofNat 32 0x16 := by rw [u7.regs, g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, g6_21]
    have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u7.regs, g6_27]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x48, 0x4)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m7]; exact w6_30
    have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m7]; exact w6_34
    have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m7]; exact w6_40
    have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m7]; exact w6_48
    have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m7]; exact w6_4c
    have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
    have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m7]; exact w6_54
    have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m7]; exact w6_58
    have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m7]; exact w6_5c
    have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m7]; exact w6_60
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m7]; exact w6_64
    have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m7]; exact w6_68
    have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m7]; exact w6_6c
    have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m7]; exact w6_70
    have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m7]; exact w6_74
    have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m7]; exact w6_78
    have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m7]; exact w6_7c
    have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m7]; exact w6_80
    have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m7]; exact w6_84
    have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m7]; exact w6_88
    have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m7]; exact w6_8c
    have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m7]; exact w6_90
    have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m7]; exact w6_94
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
    clear w6_a44 w6_a40 w6_a3c w6_a38 w6_a34 w6_a30 w6_a2c w6_a28 w6_a24 w6_a20 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_40 w6_34 w6_30 g6_20 g6_27 g6_26 g6_25 g6_21 g6_19 g6_18 g6_10 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hz_4 h0'), sv_fail F E7 s7 t7 (fun x hx => (fR7 x hx).trans (fM x hx).symm) V7 hret g7_2 g7_18 hO g7_3 g7_4⟩
  -- 0x9C6: branch, not taken
  obtain ⟨n5, d5, u5⟩ := s4.notTaken E4.self 0x9CA sv_at_9c6
    (by decide) (by rw [g4_10, s4.zero]; exact br_beq_f hz_4)
  have s5 : St n5.mem SV n5 0x9CA (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
  have g5_9 : reg n5 (9 : Fin 32) = x9 := by rw [u5.regs, g4_9]
  have g5_10 : reg n5 a0 = sl0 := by rw [u5.regs, g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x48, 0x4)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m5]; exact w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m5]; exact w4_34
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m5]; exact w4_40
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m5]; exact w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m5]; exact w4_4c
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m5]; exact w4_54
  have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m5]; exact w4_58
  have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m5]; exact w4_5c
  have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m5]; exact w4_60
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m5]; exact w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m5]; exact w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m5]; exact w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m5]; exact w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m5]; exact w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m5]; exact w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m5]; exact w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m5]; exact w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m5]; exact w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m5]; exact w4_8c
  have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m5]; exact w4_90
  have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m5]; exact w4_94
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
  clear w4_48 w4_a44 w4_a40 w4_a3c w4_a38 w4_a34 w4_a30 w4_a2c w4_a28 w4_a24 w4_a20 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_40 w4_34 w4_30 g4_27 g4_26 g4_25 g4_21 g4_19 g4_18 g4_10 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 rg4 W4 K4 fr4 s4 d4
  -- 0x9CA: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_9ca (off' := 0x9CE) (by decide)
    (by rw [g5_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0x9CE (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = x9 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_10 : reg n6 a0 = sl2 := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr, w5_a28]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x48, 0x4)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m6]; exact w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m6]; exact w5_34
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m6]; exact w5_40
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m6]; exact w5_48
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m6]; exact w5_4c
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
  have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m6]; exact w5_54
  have w6_58 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m6]; exact w5_58
  have w6_5c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m6]; exact w5_5c
  have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m6]; exact w5_60
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m6]; exact w5_64
  have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m6]; exact w5_68
  have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m6]; exact w5_6c
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m6]; exact w5_70
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m6]; exact w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m6]; exact w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m6]; exact w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m6]; exact w5_84
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m6]; exact w5_88
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m6]; exact w5_8c
  have w6_90 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m6]; exact w5_90
  have w6_94 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m6]; exact w5_94
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
  clear w5_a44 w5_a40 w5_a3c w5_a38 w5_a34 w5_a30 w5_a2c w5_a28 w5_a24 w5_a20 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_40 w5_34 w5_30 g5_27 g5_26 g5_25 g5_21 g5_19 g5_18 g5_10 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x9CE: sw
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := sv_sw F E6 s6 sv_at_9ce (off' := 0x9D0) (c := 0x44)
    (by decide) (by rw [g6_2]; sv_addr) (by decide) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_9 : reg n7 (9 : Fin 32) = x9 := by rw [rg7 (9 : Fin 32), g6_9]
  have g7_10 : reg n7 a0 = sl2 := by rw [rg7 a0, g6_10]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rg7 (18 : Fin 32), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rg7 (19 : Fin 32), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [rg7 (21 : Fin 32), g6_21]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [rg7 (25 : Fin 32), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [rg7 (26 : Fin 32), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg7 (27 : Fin 32), g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x48, 0x4), (0x44, 0x4)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K7.w32 (by decide) (by decide)).trans w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K7.w32 (by decide) (by decide)).trans w6_34
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K7.w32 (by decide) (by decide)).trans w6_40
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K7.w32 (by decide) (by decide)).trans w6_48
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K7.w32 (by decide) (by decide)).trans w6_4c
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K7.w32 (by decide) (by decide)).trans w6_50
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K7.w32 (by decide) (by decide)).trans w6_54
  have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K7.w32 (by decide) (by decide)).trans w6_58
  have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K7.w32 (by decide) (by decide)).trans w6_5c
  have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K7.w32 (by decide) (by decide)).trans w6_60
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K7.w32 (by decide) (by decide)).trans w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K7.w32 (by decide) (by decide)).trans w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K7.w32 (by decide) (by decide)).trans w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K7.w32 (by decide) (by decide)).trans w6_70
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K7.w32 (by decide) (by decide)).trans w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K7.w32 (by decide) (by decide)).trans w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K7.w32 (by decide) (by decide)).trans w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K7.w32 (by decide) (by decide)).trans w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K7.w32 (by decide) (by decide)).trans w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K7.w32 (by decide) (by decide)).trans w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K7.w32 (by decide) (by decide)).trans w6_8c
  have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K7.w32 (by decide) (by decide)).trans w6_90
  have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K7.w32 (by decide) (by decide)).trans w6_94
  have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K7.w32 (by decide) (by decide)).trans w6_a20
  have w7_a24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K7.w32 (by decide) (by decide)).trans w6_a24
  have w7_a28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K7.w32 (by decide) (by decide)).trans w6_a28
  have w7_a2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K7.w32 (by decide) (by decide)).trans w6_a2c
  have w7_a30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K7.w32 (by decide) (by decide)).trans w6_a30
  have w7_a34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K7.w32 (by decide) (by decide)).trans w6_a34
  have w7_a38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K7.w32 (by decide) (by decide)).trans w6_a38
  have w7_a3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K7.w32 (by decide) (by decide)).trans w6_a3c
  have w7_a40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K7.w32 (by decide) (by decide)).trans w6_a40
  have w7_a44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K7.w32 (by decide) (by decide)).trans w6_a44
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [W7, g6_10]
  clear w6_a44 w6_a40 w6_a3c w6_a38 w6_a34 w6_a30 w6_a2c w6_a28 w6_a24 w6_a20 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_40 w6_34 w6_30 g6_10 g6_27 g6_26 g6_25 g6_21 g6_19 g6_18 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  by_cases hz_7 : sl2 ≠ 0
  rotate_left
  · -- 0x9D0: branch, taken
    obtain ⟨n8, d8, u8⟩ := s7.taken E7.self 0xB32 sv_at_9d0
      (by decide) (by rw [g7_10, s7.zero]; exact br_beq_t (Decidable.of_not_not hz_7))
    have s8 : St n8.mem SV n8 0xB32 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
    have g8_9 : reg n8 (9 : Fin 32) = x9 := by rw [u8.regs, g7_9]
    have g8_10 : reg n8 a0 = sl2 := by rw [u8.regs, g7_10]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, g7_21]
    have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u8.regs, g7_27]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x48, 0x4), (0x44, 0x4)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m8]; exact w7_30
    have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m8]; exact w7_34
    have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m8]; exact w7_40
    have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m8]; exact w7_44
    have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m8]; exact w7_48
    have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m8]; exact w7_4c
    have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
    have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m8]; exact w7_54
    have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m8]; exact w7_58
    have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m8]; exact w7_5c
    have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m8]; exact w7_60
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m8]; exact w7_64
    have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m8]; exact w7_68
    have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m8]; exact w7_6c
    have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m8]; exact w7_70
    have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m8]; exact w7_74
    have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m8]; exact w7_78
    have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m8]; exact w7_7c
    have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m8]; exact w7_80
    have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m8]; exact w7_84
    have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m8]; exact w7_88
    have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m8]; exact w7_8c
    have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m8]; exact w7_90
    have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m8]; exact w7_94
    have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m8]; exact w7_a20
    have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m8]; exact w7_a24
    have w8_a28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m8]; exact w7_a28
    have w8_a2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m8]; exact w7_a2c
    have w8_a30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m8]; exact w7_a30
    have w8_a34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m8]; exact w7_a34
    have w8_a38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m8]; exact w7_a38
    have w8_a3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m8]; exact w7_a3c
    have w8_a40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m8]; exact w7_a40
    have w8_a44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m8]; exact w7_a44
    clear w7_44 w7_a44 w7_a40 w7_a3c w7_a38 w7_a34 w7_a30 w7_a2c w7_a28 w7_a24 w7_a20 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_40 w7_34 w7_30 g7_27 g7_26 g7_25 g7_21 g7_19 g7_18 g7_10 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
    -- 0xB32
    obtain ⟨n9, c9, u9⟩ := s8.block svL7b32 E8.self svL7b32_end
      ⟨trivial, trivial⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have s9 : St n9.mem SV n9 0xB34 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have rb9 : ∀ q, reg n9 q = (runBlock svL7b32 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
    have g9_9 : reg n9 (9 : Fin 32) = x9 := by
      rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
    have g9_10 : reg n9 a0 = sl2 := by
      rw [rb9, runBlock_reg _ _ _ a0 s8.zero (by decide), g8_10]
    have g9_18 : reg n9 (18 : Fin 32) = out := by
      rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by
      rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by
      rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
    have g9_25 : reg n9 (25 : Fin 32) = x25 := by
      rw [rb9, runBlock_reg _ _ _ (25 : Fin 32) s8.zero (by decide), g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = x26 := by
      rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
    have g9_20 : reg n9 (20 : Fin 32) = BitVec.ofNat 32 0x16 := by
      rw [rb9]; simp +decide only [runBlock, BInstr.run, svL7b32, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g8_2, g8_3, g8_4, g8_9, g8_10, g8_18, g8_19, g8_21, g8_25, g8_26, g8_27, s8.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x48, 0x4), (0x44, 0x4)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m9]; exact w8_30
    have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m9]; exact w8_34
    have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m9]; exact w8_40
    have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m9]; exact w8_44
    have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m9]; exact w8_48
    have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m9]; exact w8_4c
    have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
    have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m9]; exact w8_54
    have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m9]; exact w8_58
    have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m9]; exact w8_5c
    have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m9]; exact w8_60
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m9]; exact w8_64
    have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m9]; exact w8_68
    have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m9]; exact w8_6c
    have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m9]; exact w8_70
    have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m9]; exact w8_74
    have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m9]; exact w8_78
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m9]; exact w8_7c
    have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m9]; exact w8_80
    have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m9]; exact w8_84
    have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m9]; exact w8_88
    have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m9]; exact w8_8c
    have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m9]; exact w8_90
    have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m9]; exact w8_94
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
    clear w8_a44 w8_a40 w8_a3c w8_a38 w8_a34 w8_a30 w8_a2c w8_a28 w8_a24 w8_a20 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_44 w8_40 w8_34 w8_30 g8_27 g8_26 g8_25 g8_21 g8_19 g8_18 g8_10 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    -- 0xB34: j
    obtain ⟨n10, d10, u10⟩ := s9.jump E9.self sv_at_b34 (off' := 0x966) (by decide)
      (by rw [s9.pc]; decide)
    have s10 : St n10.mem SV n10 0x966 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
    have g10_9 : reg n10 (9 : Fin 32) = x9 := by rw [u10.regs, g9_9]
    have g10_10 : reg n10 a0 = sl2 := by rw [u10.regs, g9_10]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = BitVec.ofNat 32 0x16 := by rw [u10.regs, g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, g9_21]
    have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, g9_27]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x48, 0x4), (0x44, 0x4)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m10]; exact w9_30
    have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m10]; exact w9_34
    have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m10]; exact w9_40
    have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m10]; exact w9_44
    have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m10]; exact w9_48
    have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m10]; exact w9_4c
    have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
    have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m10]; exact w9_54
    have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m10]; exact w9_58
    have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m10]; exact w9_5c
    have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m10]; exact w9_60
    have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m10]; exact w9_64
    have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m10]; exact w9_68
    have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m10]; exact w9_6c
    have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m10]; exact w9_70
    have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m10]; exact w9_74
    have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m10]; exact w9_78
    have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m10]; exact w9_7c
    have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m10]; exact w9_80
    have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m10]; exact w9_84
    have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m10]; exact w9_88
    have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m10]; exact w9_8c
    have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m10]; exact w9_90
    have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m10]; exact w9_94
    have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m10]; exact w9_a20
    have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m10]; exact w9_a24
    have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m10]; exact w9_a28
    have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m10]; exact w9_a2c
    have w10_a30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m10]; exact w9_a30
    have w10_a34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m10]; exact w9_a34
    have w10_a38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m10]; exact w9_a38
    have w10_a3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m10]; exact w9_a3c
    have w10_a40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m10]; exact w9_a40
    have w10_a44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m10]; exact w9_a44
    clear w9_a44 w9_a40 w9_a3c w9_a38 w9_a34 w9_a30 w9_a2c w9_a28 w9_a24 w9_a20 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_44 w9_40 w9_34 w9_30 g9_20 g9_27 g9_26 g9_25 g9_21 g9_19 g9_18 g9_10 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
    exact .inl ⟨(fun ⟨h0', h1', _⟩ => by exact hz_7 h1'), sv_fail F E10 s10 t10 (fun x hx => (fR10 x hx).trans (fM x hx).symm) V10 hret g10_2 g10_18 hO g10_3 g10_4⟩
  -- 0x9D0: branch, not taken
  obtain ⟨n8, d8, u8⟩ := s7.notTaken E7.self 0x9D4 sv_at_9d0
    (by decide) (by rw [g7_10, s7.zero]; exact br_beq_f hz_7)
  have s8 : St n8.mem SV n8 0x9D4 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
  have g8_9 : reg n8 (9 : Fin 32) = x9 := by rw [u8.regs, g7_9]
  have g8_10 : reg n8 a0 = sl2 := by rw [u8.regs, g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, g7_21]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u8.regs, g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x48, 0x4), (0x44, 0x4)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m8]; exact w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m8]; exact w7_34
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m8]; exact w7_40
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m8]; exact w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m8]; exact w7_48
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m8]; exact w7_4c
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
  have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m8]; exact w7_54
  have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m8]; exact w7_58
  have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m8]; exact w7_5c
  have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m8]; exact w7_60
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m8]; exact w7_64
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m8]; exact w7_68
  have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m8]; exact w7_6c
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m8]; exact w7_70
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m8]; exact w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m8]; exact w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m8]; exact w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m8]; exact w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m8]; exact w7_84
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m8]; exact w7_88
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m8]; exact w7_8c
  have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m8]; exact w7_90
  have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m8]; exact w7_94
  have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m8]; exact w7_a20
  have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m8]; exact w7_a24
  have w8_a28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m8]; exact w7_a28
  have w8_a2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m8]; exact w7_a2c
  have w8_a30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m8]; exact w7_a30
  have w8_a34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m8]; exact w7_a34
  have w8_a38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m8]; exact w7_a38
  have w8_a3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m8]; exact w7_a3c
  have w8_a40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m8]; exact w7_a40
  have w8_a44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m8]; exact w7_a44
  clear w7_44 w7_a44 w7_a40 w7_a3c w7_a38 w7_a34 w7_a30 w7_a2c w7_a28 w7_a24 w7_a20 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_40 w7_34 w7_30 g7_27 g7_26 g7_25 g7_21 g7_19 g7_18 g7_10 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0x9D4: lw
  obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_9d4 (off' := 0x9D8) (by decide)
    (by rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x10 = B + 0x21A0 + BitVec.ofNat 32 0xA30 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s9 : St n9.mem SV n9 0x9D8 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
  have g9_9 : reg n9 (9 : Fin 32) = x9 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
  have g9_10 : reg n9 a0 = sl4 := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x10 = B + 0x21A0 + BitVec.ofNat 32 0xA30 by sv_addr, w8_a30]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x48, 0x4), (0x44, 0x4)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m9]; exact w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m9]; exact w8_34
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m9]; exact w8_40
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m9]; exact w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m9]; exact w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m9]; exact w8_4c
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m9]; exact w8_54
  have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m9]; exact w8_58
  have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m9]; exact w8_5c
  have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m9]; exact w8_60
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m9]; exact w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m9]; exact w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m9]; exact w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m9]; exact w8_70
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m9]; exact w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m9]; exact w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m9]; exact w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m9]; exact w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m9]; exact w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m9]; exact w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m9]; exact w8_8c
  have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m9]; exact w8_90
  have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m9]; exact w8_94
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
  clear w8_a44 w8_a40 w8_a3c w8_a38 w8_a34 w8_a30 w8_a2c w8_a28 w8_a24 w8_a20 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_44 w8_40 w8_34 w8_30 g8_27 g8_26 g8_25 g8_21 g8_19 g8_18 g8_10 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0x9D8: sw
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_9d8 (off' := 0x9DA) (c := 0x40)
    (by decide) (by rw [g9_2]; sv_addr) (by decide) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_9 : reg n10 (9 : Fin 32) = x9 := by rw [rg10 (9 : Fin 32), g9_9]
  have g10_10 : reg n10 a0 = sl4 := by rw [rg10 a0, g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rg10 (18 : Fin 32), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rg10 (19 : Fin 32), g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [rg10 (21 : Fin 32), g9_21]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [rg10 (25 : Fin 32), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [rg10 (26 : Fin 32), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg10 (27 : Fin 32), g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K10.w32 (by decide) (by decide)).trans w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K10.w32 (by decide) (by decide)).trans w9_34
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := (K10.w32 (by decide) (by decide)).trans w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K10.w32 (by decide) (by decide)).trans w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K10.w32 (by decide) (by decide)).trans w9_4c
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K10.w32 (by decide) (by decide)).trans w9_50
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K10.w32 (by decide) (by decide)).trans w9_54
  have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K10.w32 (by decide) (by decide)).trans w9_58
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K10.w32 (by decide) (by decide)).trans w9_5c
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K10.w32 (by decide) (by decide)).trans w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K10.w32 (by decide) (by decide)).trans w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K10.w32 (by decide) (by decide)).trans w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K10.w32 (by decide) (by decide)).trans w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K10.w32 (by decide) (by decide)).trans w9_70
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K10.w32 (by decide) (by decide)).trans w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K10.w32 (by decide) (by decide)).trans w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K10.w32 (by decide) (by decide)).trans w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K10.w32 (by decide) (by decide)).trans w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K10.w32 (by decide) (by decide)).trans w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K10.w32 (by decide) (by decide)).trans w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K10.w32 (by decide) (by decide)).trans w9_8c
  have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K10.w32 (by decide) (by decide)).trans w9_90
  have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K10.w32 (by decide) (by decide)).trans w9_94
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
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [W10, g9_10]
  clear w9_a44 w9_a40 w9_a3c w9_a38 w9_a34 w9_a30 w9_a2c w9_a28 w9_a24 w9_a20 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_44 w9_40 w9_34 w9_30 g9_10 g9_27 g9_26 g9_25 g9_21 g9_19 g9_18 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  by_cases hz_10 : sl4 ≠ 0
  rotate_left
  · -- 0x9DA: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0xB32 sv_at_9da
      (by decide) (by rw [g10_10, s10.zero]; exact br_beq_t (Decidable.of_not_not hz_10))
    have s11 : St n11.mem SV n11 0xB32 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_9 : reg n11 (9 : Fin 32) = x9 := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = sl4 := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m11]; exact w10_30
    have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m11]; exact w10_34
    have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m11]; exact w10_40
    have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m11]; exact w10_44
    have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m11]; exact w10_48
    have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m11]; exact w10_4c
    have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
    have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m11]; exact w10_54
    have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m11]; exact w10_58
    have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m11]; exact w10_5c
    have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m11]; exact w10_60
    have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m11]; exact w10_64
    have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m11]; exact w10_68
    have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m11]; exact w10_6c
    have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m11]; exact w10_70
    have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m11]; exact w10_74
    have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m11]; exact w10_78
    have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m11]; exact w10_7c
    have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m11]; exact w10_80
    have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m11]; exact w10_84
    have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m11]; exact w10_88
    have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m11]; exact w10_8c
    have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m11]; exact w10_90
    have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m11]; exact w10_94
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
    clear w10_40 w10_a44 w10_a40 w10_a3c w10_a38 w10_a34 w10_a30 w10_a2c w10_a28 w10_a24 w10_a20 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_34 w10_30 g10_27 g10_26 g10_25 g10_21 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
    -- 0xB32
    obtain ⟨n12, c12, u12⟩ := s11.block svL7b32 E11.self svL7b32_end
      ⟨trivial, trivial⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have s12 : St n12.mem SV n12 0xB34 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have rb12 : ∀ q, reg n12 q = (runBlock svL7b32 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans c12
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by
      rw [rb12, runBlock_reg _ _ _ sp s11.zero (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb12, runBlock_reg _ _ _ (3 : Fin 32) s11.zero (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb12, runBlock_reg _ _ _ (4 : Fin 32) s11.zero (by decide), g11_4]
    have g12_9 : reg n12 (9 : Fin 32) = x9 := by
      rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
    have g12_10 : reg n12 a0 = sl4 := by
      rw [rb12, runBlock_reg _ _ _ a0 s11.zero (by decide), g11_10]
    have g12_18 : reg n12 (18 : Fin 32) = out := by
      rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by
      rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by
      rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
    have g12_25 : reg n12 (25 : Fin 32) = x25 := by
      rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by
      rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
    have g12_20 : reg n12 (20 : Fin 32) = BitVec.ofNat 32 0x16 := by
      rw [rb12]; simp +decide only [runBlock, BInstr.run, svL7b32, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g11_2, g11_3, g11_4, g11_9, g11_10, g11_18, g11_19, g11_21, g11_25, g11_26, g11_27, s11.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m12]; exact w11_30
    have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m12]; exact w11_34
    have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m12]; exact w11_40
    have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m12]; exact w11_44
    have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m12]; exact w11_48
    have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m12]; exact w11_4c
    have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
    have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m12]; exact w11_54
    have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m12]; exact w11_58
    have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m12]; exact w11_5c
    have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m12]; exact w11_60
    have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m12]; exact w11_64
    have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m12]; exact w11_68
    have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m12]; exact w11_6c
    have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m12]; exact w11_70
    have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m12]; exact w11_74
    have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m12]; exact w11_78
    have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m12]; exact w11_7c
    have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m12]; exact w11_80
    have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m12]; exact w11_84
    have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m12]; exact w11_88
    have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m12]; exact w11_8c
    have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m12]; exact w11_90
    have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m12]; exact w11_94
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
    clear w11_a44 w11_a40 w11_a3c w11_a38 w11_a34 w11_a30 w11_a2c w11_a28 w11_a24 w11_a20 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_34 w11_30 g11_27 g11_26 g11_25 g11_21 g11_19 g11_18 g11_10 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    -- 0xB34: j
    obtain ⟨n13, d13, u13⟩ := s12.jump E12.self sv_at_b34 (off' := 0x966) (by decide)
      (by rw [s12.pc]; decide)
    have s13 : St n13.mem SV n13 0x966 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
    have t13 : Steps n0 n13 := t12.trans (.single d13)
    have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
    have E13 : SvCode n13.mem := E12.fr F fr13
    have V13 : SvSaves B n13.mem v := V12.same m13
    have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
    have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
    have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
    have g13_9 : reg n13 (9 : Fin 32) = x9 := by rw [u13.regs, g12_9]
    have g13_10 : reg n13 a0 = sl4 := by rw [u13.regs, g12_10]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = BitVec.ofNat 32 0x16 := by rw [u13.regs, g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u13.regs, g12_27]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m13]; exact w12_30
    have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m13]; exact w12_34
    have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m13]; exact w12_40
    have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m13]; exact w12_44
    have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m13]; exact w12_48
    have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m13]; exact w12_4c
    have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
    have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m13]; exact w12_54
    have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m13]; exact w12_58
    have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m13]; exact w12_5c
    have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m13]; exact w12_60
    have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m13]; exact w12_64
    have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m13]; exact w12_68
    have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m13]; exact w12_6c
    have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m13]; exact w12_70
    have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m13]; exact w12_74
    have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m13]; exact w12_78
    have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m13]; exact w12_7c
    have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m13]; exact w12_80
    have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m13]; exact w12_84
    have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m13]; exact w12_88
    have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m13]; exact w12_8c
    have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m13]; exact w12_90
    have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m13]; exact w12_94
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
    clear w12_a44 w12_a40 w12_a3c w12_a38 w12_a34 w12_a30 w12_a2c w12_a28 w12_a24 w12_a20 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_44 w12_40 w12_34 w12_30 g12_20 g12_27 g12_26 g12_25 g12_21 g12_19 g12_18 g12_10 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
    exact .inl ⟨(fun ⟨h0', h1', h2', _⟩ => by exact hz_10 h2'), sv_fail F E13 s13 t13 (fun x hx => (fR13 x hx).trans (fM x hx).symm) V13 hret g13_2 g13_18 hO g13_3 g13_4⟩
  -- 0x9DA: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0x9DE sv_at_9da
    (by decide) (by rw [g10_10, s10.zero]; exact br_beq_f hz_10)
  have s11 : St n11.mem SV n11 0x9DE (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_9 : reg n11 (9 : Fin 32) = x9 := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = sl4 := by rw [u11.regs, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m11]; exact w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m11]; exact w10_34
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m11]; exact w10_40
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m11]; exact w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m11]; exact w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m11]; exact w10_4c
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
  have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m11]; exact w10_54
  have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m11]; exact w10_58
  have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m11]; exact w10_5c
  have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m11]; exact w10_60
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m11]; exact w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m11]; exact w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m11]; exact w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m11]; exact w10_70
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m11]; exact w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m11]; exact w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m11]; exact w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m11]; exact w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m11]; exact w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m11]; exact w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m11]; exact w10_8c
  have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m11]; exact w10_90
  have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m11]; exact w10_94
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
  clear w10_40 w10_a44 w10_a40 w10_a3c w10_a38 w10_a34 w10_a30 w10_a2c w10_a28 w10_a24 w10_a20 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_34 w10_30 g10_27 g10_26 g10_25 g10_21 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0x9DE: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_9de (off' := 0x9E2) (by decide)
    (by rw [g11_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x18 = B + 0x21A0 + BitVec.ofNat 32 0xA38 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x9E2 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_9 : reg n12 (9 : Fin 32) = x9 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_10 : reg n12 a0 = sl6 := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x18 = B + 0x21A0 + BitVec.ofNat 32 0xA38 by sv_addr, w11_a38]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m12]; exact w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m12]; exact w11_34
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m12]; exact w11_40
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m12]; exact w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m12]; exact w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m12]; exact w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
  have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m12]; exact w11_54
  have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m12]; exact w11_58
  have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m12]; exact w11_5c
  have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m12]; exact w11_60
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m12]; exact w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m12]; exact w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m12]; exact w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m12]; exact w11_70
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m12]; exact w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m12]; exact w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m12]; exact w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m12]; exact w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m12]; exact w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m12]; exact w11_8c
  have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m12]; exact w11_90
  have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m12]; exact w11_94
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
  clear w11_a44 w11_a40 w11_a3c w11_a38 w11_a34 w11_a30 w11_a2c w11_a28 w11_a24 w11_a20 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_34 w11_30 g11_27 g11_26 g11_25 g11_21 g11_19 g11_18 g11_10 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x9E2: sw
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := sv_sw F E12 s12 sv_at_9e2 (off' := 0x9E4) (c := 0x3C)
    (by decide) (by rw [g12_2]; sv_addr) (by decide) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_9 : reg n13 (9 : Fin 32) = x9 := by rw [rg13 (9 : Fin 32), g12_9]
  have g13_10 : reg n13 a0 = sl6 := by rw [rg13 a0, g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rg13 (18 : Fin 32), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rg13 (19 : Fin 32), g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [rg13 (21 : Fin 32), g12_21]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [rg13 (25 : Fin 32), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [rg13 (26 : Fin 32), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg13 (27 : Fin 32), g12_27]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K13.w32 (by decide) (by decide)).trans w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K13.w32 (by decide) (by decide)).trans w12_34
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := (K13.w32 (by decide) (by decide)).trans w12_40
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := (K13.w32 (by decide) (by decide)).trans w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K13.w32 (by decide) (by decide)).trans w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K13.w32 (by decide) (by decide)).trans w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K13.w32 (by decide) (by decide)).trans w12_50
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K13.w32 (by decide) (by decide)).trans w12_54
  have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K13.w32 (by decide) (by decide)).trans w12_58
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K13.w32 (by decide) (by decide)).trans w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K13.w32 (by decide) (by decide)).trans w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K13.w32 (by decide) (by decide)).trans w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K13.w32 (by decide) (by decide)).trans w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K13.w32 (by decide) (by decide)).trans w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K13.w32 (by decide) (by decide)).trans w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K13.w32 (by decide) (by decide)).trans w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K13.w32 (by decide) (by decide)).trans w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K13.w32 (by decide) (by decide)).trans w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K13.w32 (by decide) (by decide)).trans w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K13.w32 (by decide) (by decide)).trans w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K13.w32 (by decide) (by decide)).trans w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K13.w32 (by decide) (by decide)).trans w12_8c
  have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K13.w32 (by decide) (by decide)).trans w12_90
  have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K13.w32 (by decide) (by decide)).trans w12_94
  have w13_a20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K13.w32 (by decide) (by decide)).trans w12_a20
  have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K13.w32 (by decide) (by decide)).trans w12_a24
  have w13_a28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K13.w32 (by decide) (by decide)).trans w12_a28
  have w13_a2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K13.w32 (by decide) (by decide)).trans w12_a2c
  have w13_a30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K13.w32 (by decide) (by decide)).trans w12_a30
  have w13_a34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K13.w32 (by decide) (by decide)).trans w12_a34
  have w13_a38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K13.w32 (by decide) (by decide)).trans w12_a38
  have w13_a3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K13.w32 (by decide) (by decide)).trans w12_a3c
  have w13_a40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K13.w32 (by decide) (by decide)).trans w12_a40
  have w13_a44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K13.w32 (by decide) (by decide)).trans w12_a44
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [W13, g12_10]
  clear w12_a44 w12_a40 w12_a3c w12_a38 w12_a34 w12_a30 w12_a2c w12_a28 w12_a24 w12_a20 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_44 w12_40 w12_34 w12_30 g12_10 g12_27 g12_26 g12_25 g12_21 g12_19 g12_18 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  by_cases hz_13 : sl6 ≠ 0
  rotate_left
  · -- 0x9E4: branch, taken
    obtain ⟨n14, d14, u14⟩ := s13.taken E13.self 0xB32 sv_at_9e4
      (by decide) (by rw [g13_10, s13.zero]; exact br_beq_t (Decidable.of_not_not hz_13))
    have s14 : St n14.mem SV n14 0xB32 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
    have t14 : Steps n0 n14 := t13.trans (.single d14)
    have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
    have E14 : SvCode n14.mem := E13.fr F fr14
    have V14 : SvSaves B n14.mem v := V13.same m14
    have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, g13_2]
    have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, g13_3]
    have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, g13_4]
    have g14_9 : reg n14 (9 : Fin 32) = x9 := by rw [u14.regs, g13_9]
    have g14_10 : reg n14 a0 = sl6 := by rw [u14.regs, g13_10]
    have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, g13_19]
    have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [u14.regs, g13_21]
    have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [u14.regs, g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [u14.regs, g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u14.regs, g13_27]
    have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4)] := by rw [m14]; exact keep_kk13
    clear keep_kk13
    have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m14]; exact w13_30
    have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m14]; exact w13_34
    have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m14]; exact w13_3c
    have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m14]; exact w13_40
    have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m14]; exact w13_44
    have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m14]; exact w13_48
    have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m14]; exact w13_4c
    have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m14]; exact w13_50
    have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m14]; exact w13_54
    have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m14]; exact w13_58
    have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m14]; exact w13_5c
    have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m14]; exact w13_60
    have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m14]; exact w13_64
    have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m14]; exact w13_68
    have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m14]; exact w13_6c
    have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m14]; exact w13_70
    have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m14]; exact w13_74
    have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m14]; exact w13_78
    have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m14]; exact w13_7c
    have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m14]; exact w13_80
    have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m14]; exact w13_84
    have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m14]; exact w13_88
    have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m14]; exact w13_8c
    have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m14]; exact w13_90
    have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m14]; exact w13_94
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
    clear w13_3c w13_a44 w13_a40 w13_a3c w13_a38 w13_a34 w13_a30 w13_a2c w13_a28 w13_a24 w13_a20 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_44 w13_40 w13_34 w13_30 g13_27 g13_26 g13_25 g13_21 g13_19 g13_18 g13_10 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
    -- 0xB32
    obtain ⟨n15, c15, u15⟩ := s14.block svL7b32 E14.self svL7b32_end
      ⟨trivial, trivial⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have s15 : St n15.mem SV n15 0xB34 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have rb15 : ∀ q, reg n15 q = (runBlock svL7b32 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
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
    have g15_9 : reg n15 (9 : Fin 32) = x9 := by
      rw [rb15, runBlock_reg _ _ _ (9 : Fin 32) s14.zero (by decide), g14_9]
    have g15_10 : reg n15 a0 = sl6 := by
      rw [rb15, runBlock_reg _ _ _ a0 s14.zero (by decide), g14_10]
    have g15_18 : reg n15 (18 : Fin 32) = out := by
      rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by
      rw [rb15, runBlock_reg _ _ _ (19 : Fin 32) s14.zero (by decide), g14_19]
    have g15_21 : reg n15 (21 : Fin 32) = x21 := by
      rw [rb15, runBlock_reg _ _ _ (21 : Fin 32) s14.zero (by decide), g14_21]
    have g15_25 : reg n15 (25 : Fin 32) = x25 := by
      rw [rb15, runBlock_reg _ _ _ (25 : Fin 32) s14.zero (by decide), g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = x26 := by
      rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb15, runBlock_reg _ _ _ (27 : Fin 32) s14.zero (by decide), g14_27]
    have g15_20 : reg n15 (20 : Fin 32) = BitVec.ofNat 32 0x16 := by
      rw [rb15]; simp +decide only [runBlock, BInstr.run, svL7b32, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g14_2, g14_3, g14_4, g14_9, g14_10, g14_18, g14_19, g14_21, g14_25, g14_26, g14_27, s14.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4)] := by rw [m15]; exact keep_kk14
    clear keep_kk14
    have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m15]; exact w14_30
    have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m15]; exact w14_34
    have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m15]; exact w14_3c
    have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m15]; exact w14_40
    have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m15]; exact w14_44
    have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m15]; exact w14_48
    have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m15]; exact w14_4c
    have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m15]; exact w14_50
    have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m15]; exact w14_54
    have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m15]; exact w14_58
    have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m15]; exact w14_5c
    have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m15]; exact w14_60
    have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m15]; exact w14_64
    have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m15]; exact w14_68
    have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m15]; exact w14_6c
    have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m15]; exact w14_70
    have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m15]; exact w14_74
    have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m15]; exact w14_78
    have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m15]; exact w14_7c
    have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m15]; exact w14_80
    have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m15]; exact w14_84
    have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m15]; exact w14_88
    have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m15]; exact w14_8c
    have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m15]; exact w14_90
    have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m15]; exact w14_94
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
    clear w14_a44 w14_a40 w14_a3c w14_a38 w14_a34 w14_a30 w14_a2c w14_a28 w14_a24 w14_a20 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_34 w14_30 g14_27 g14_26 g14_25 g14_21 g14_19 g14_18 g14_10 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
    -- 0xB34: j
    obtain ⟨n16, d16, u16⟩ := s15.jump E15.self sv_at_b34 (off' := 0x966) (by decide)
      (by rw [s15.pc]; decide)
    have s16 : St n16.mem SV n16 0x966 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
    have g16_9 : reg n16 (9 : Fin 32) = x9 := by rw [u16.regs, g15_9]
    have g16_10 : reg n16 a0 = sl6 := by rw [u16.regs, g15_10]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = BitVec.ofNat 32 0x16 := by rw [u16.regs, g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, g15_21]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, g15_27]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m16]; exact w15_30
    have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m16]; exact w15_34
    have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m16]; exact w15_3c
    have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m16]; exact w15_40
    have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m16]; exact w15_44
    have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m16]; exact w15_48
    have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m16]; exact w15_4c
    have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
    have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m16]; exact w15_54
    have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m16]; exact w15_58
    have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m16]; exact w15_5c
    have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m16]; exact w15_60
    have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m16]; exact w15_64
    have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m16]; exact w15_68
    have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m16]; exact w15_6c
    have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m16]; exact w15_70
    have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m16]; exact w15_74
    have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m16]; exact w15_78
    have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m16]; exact w15_7c
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m16]; exact w15_80
    have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m16]; exact w15_84
    have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m16]; exact w15_88
    have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m16]; exact w15_8c
    have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m16]; exact w15_90
    have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m16]; exact w15_94
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
    clear w15_a44 w15_a40 w15_a3c w15_a38 w15_a34 w15_a30 w15_a2c w15_a28 w15_a24 w15_a20 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_34 w15_30 g15_20 g15_27 g15_26 g15_25 g15_21 g15_19 g15_18 g15_10 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
    exact .inl ⟨(fun ⟨h0', h1', h2', h3', _⟩ => by exact hz_13 h3'), sv_fail F E16 s16 t16 (fun x hx => (fR16 x hx).trans (fM x hx).symm) V16 hret g16_2 g16_18 hO g16_3 g16_4⟩
  -- 0x9E4: branch, not taken
  obtain ⟨n14, d14, u14⟩ := s13.notTaken E13.self 0x9E8 sv_at_9e4
    (by decide) (by rw [g13_10, s13.zero]; exact br_beq_f hz_13)
  have s14 : St n14.mem SV n14 0x9E8 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, g13_4]
  have g14_9 : reg n14 (9 : Fin 32) = x9 := by rw [u14.regs, g13_9]
  have g14_10 : reg n14 a0 = sl6 := by rw [u14.regs, g13_10]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, g13_19]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [u14.regs, g13_21]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [u14.regs, g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [u14.regs, g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u14.regs, g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m14]; exact w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m14]; exact w13_34
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m14]; exact w13_3c
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m14]; exact w13_40
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m14]; exact w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m14]; exact w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m14]; exact w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m14]; exact w13_50
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m14]; exact w13_54
  have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m14]; exact w13_58
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m14]; exact w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m14]; exact w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m14]; exact w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m14]; exact w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m14]; exact w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m14]; exact w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m14]; exact w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m14]; exact w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m14]; exact w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m14]; exact w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m14]; exact w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m14]; exact w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m14]; exact w13_8c
  have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m14]; exact w13_90
  have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m14]; exact w13_94
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
  clear w13_3c w13_a44 w13_a40 w13_a3c w13_a38 w13_a34 w13_a30 w13_a2c w13_a28 w13_a24 w13_a20 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_44 w13_40 w13_34 w13_30 g13_27 g13_26 g13_25 g13_21 g13_19 g13_18 g13_10 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  -- 0x9E8: lw
  obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_9e8 (off' := 0x9EC) (by decide)
    (by rw [g14_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x20 = B + 0x21A0 + BitVec.ofNat 32 0xA40 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s15 : St n15.mem SV n15 0x9EC (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_9 : reg n15 (9 : Fin 32) = x9 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_10 : reg n15 a0 = sl8 := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x20 = B + 0x21A0 + BitVec.ofNat 32 0xA40 by sv_addr, w14_a40]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m15]; exact w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m15]; exact w14_34
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m15]; exact w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m15]; exact w14_40
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m15]; exact w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m15]; exact w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m15]; exact w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m15]; exact w14_50
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m15]; exact w14_54
  have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m15]; exact w14_58
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m15]; exact w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m15]; exact w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m15]; exact w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m15]; exact w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m15]; exact w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m15]; exact w14_70
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m15]; exact w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m15]; exact w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m15]; exact w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m15]; exact w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m15]; exact w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m15]; exact w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m15]; exact w14_8c
  have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m15]; exact w14_90
  have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m15]; exact w14_94
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
  clear w14_a44 w14_a40 w14_a3c w14_a38 w14_a34 w14_a30 w14_a2c w14_a28 w14_a24 w14_a20 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_34 w14_30 g14_27 g14_26 g14_25 g14_21 g14_19 g14_18 g14_10 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0x9EC: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_9ec (off' := 0x9EE) (c := 0x38)
    (by decide) (by rw [g15_2]; sv_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_9 : reg n16 (9 : Fin 32) = x9 := by rw [rg16 (9 : Fin 32), g15_9]
  have g16_10 : reg n16 a0 = sl8 := by rw [rg16 a0, g15_10]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [rg16 (21 : Fin 32), g15_21]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [rg16 (25 : Fin 32), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [rg16 (26 : Fin 32), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg16 (27 : Fin 32), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K16.w32 (by decide) (by decide)).trans w15_30
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K16.w32 (by decide) (by decide)).trans w15_34
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := (K16.w32 (by decide) (by decide)).trans w15_3c
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := (K16.w32 (by decide) (by decide)).trans w15_40
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := (K16.w32 (by decide) (by decide)).trans w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K16.w32 (by decide) (by decide)).trans w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K16.w32 (by decide) (by decide)).trans w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K16.w32 (by decide) (by decide)).trans w15_50
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K16.w32 (by decide) (by decide)).trans w15_54
  have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K16.w32 (by decide) (by decide)).trans w15_58
  have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K16.w32 (by decide) (by decide)).trans w15_5c
  have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K16.w32 (by decide) (by decide)).trans w15_60
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K16.w32 (by decide) (by decide)).trans w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K16.w32 (by decide) (by decide)).trans w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K16.w32 (by decide) (by decide)).trans w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K16.w32 (by decide) (by decide)).trans w15_70
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K16.w32 (by decide) (by decide)).trans w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K16.w32 (by decide) (by decide)).trans w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K16.w32 (by decide) (by decide)).trans w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K16.w32 (by decide) (by decide)).trans w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K16.w32 (by decide) (by decide)).trans w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K16.w32 (by decide) (by decide)).trans w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K16.w32 (by decide) (by decide)).trans w15_8c
  have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K16.w32 (by decide) (by decide)).trans w15_90
  have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K16.w32 (by decide) (by decide)).trans w15_94
  have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K16.w32 (by decide) (by decide)).trans w15_a20
  have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K16.w32 (by decide) (by decide)).trans w15_a24
  have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K16.w32 (by decide) (by decide)).trans w15_a28
  have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K16.w32 (by decide) (by decide)).trans w15_a2c
  have w16_a30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K16.w32 (by decide) (by decide)).trans w15_a30
  have w16_a34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K16.w32 (by decide) (by decide)).trans w15_a34
  have w16_a38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K16.w32 (by decide) (by decide)).trans w15_a38
  have w16_a3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K16.w32 (by decide) (by decide)).trans w15_a3c
  have w16_a40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K16.w32 (by decide) (by decide)).trans w15_a40
  have w16_a44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K16.w32 (by decide) (by decide)).trans w15_a44
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [W16, g15_10]
  clear w15_a44 w15_a40 w15_a3c w15_a38 w15_a34 w15_a30 w15_a2c w15_a28 w15_a24 w15_a20 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_34 w15_30 g15_10 g15_27 g15_26 g15_25 g15_21 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0x9EE
  obtain ⟨n17, c17, u17⟩ := s16.block svL79ee E16.self svL79ee_end
    ⟨trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x9F2 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svL79ee (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_9 : reg n17 (9 : Fin 32) = x9 := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = if BitVec.ult 0 (sl8) then (1 : Word) else 0 := by
    rw [rb17]; simp only [runBlock, BInstr.run, svL79ee, upd, aluEval]; rw [g16_10, s16.zero]; rfl
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m17]; exact w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m17]; exact w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m17]; exact w16_38
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m17]; exact w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m17]; exact w16_40
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m17]; exact w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m17]; exact w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m17]; exact w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m17]; exact w16_54
  have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m17]; exact w16_58
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m17]; exact w16_5c
  have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m17]; exact w16_60
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m17]; exact w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m17]; exact w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m17]; exact w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m17]; exact w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m17]; exact w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m17]; exact w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m17]; exact w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m17]; exact w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m17]; exact w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m17]; exact w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m17]; exact w16_8c
  have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m17]; exact w16_90
  have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m17]; exact w16_94
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
  clear w16_38 w16_a44 w16_a40 w16_a3c w16_a38 w16_a34 w16_a30 w16_a2c w16_a28 w16_a24 w16_a20 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_34 w16_30 g16_27 g16_26 g16_25 g16_21 g16_19 g16_18 g16_10 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0x9F2: lw
  obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_9f2 (off' := 0x9F4) (by decide)
    (by rw [g17_2, show B + 0x21A0 + 0x30 = B + 0x21A0 + BitVec.ofNat 32 0x30 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s18 : St n18.mem SV n18 0x9F4 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
  have g18_9 : reg n18 (9 : Fin 32) = x9 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_9]
  have g18_10 : reg n18 a0 = if BitVec.ult 0 (sl8) then (1 : Word) else 0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_10]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
  have g18_11 : reg n18 a1 = f30 := by
    rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g17_2, show B + 0x21A0 + 0x30 = B + 0x21A0 + BitVec.ofNat 32 0x30 by sv_addr, w17_30]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m18]; exact w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m18]; exact w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m18]; exact w17_38
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m18]; exact w17_3c
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m18]; exact w17_40
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m18]; exact w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m18]; exact w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m18]; exact w17_4c
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
  have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m18]; exact w17_54
  have w18_58 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m18]; exact w17_58
  have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m18]; exact w17_5c
  have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m18]; exact w17_60
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m18]; exact w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m18]; exact w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m18]; exact w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m18]; exact w17_70
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m18]; exact w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m18]; exact w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m18]; exact w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m18]; exact w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m18]; exact w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m18]; exact w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m18]; exact w17_8c
  have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m18]; exact w17_90
  have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m18]; exact w17_94
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
  clear w17_a44 w17_a40 w17_a3c w17_a38 w17_a34 w17_a30 w17_a2c w17_a28 w17_a24 w17_a20 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_34 w17_30 g17_10 g17_27 g17_26 g17_25 g17_21 g17_19 g17_18 g17_9 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x9F4: lw
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_9f4 (off' := 0x9F6) (by decide)
    (by rw [g18_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s19 : St n19.mem SV n19 0x9F6 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_9 : reg n19 (9 : Fin 32) = x9 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
  have g19_10 : reg n19 a0 = if BitVec.ult 0 (sl8) then (1 : Word) else 0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_10]
  have g19_11 : reg n19 a1 = f30 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_11]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_12 : reg n19 a2 = f34 := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr, w18_34]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m19]; exact w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m19]; exact w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m19]; exact w18_38
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m19]; exact w18_3c
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m19]; exact w18_40
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m19]; exact w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m19]; exact w18_48
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m19]; exact w18_4c
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m19]; exact w18_50
  have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m19]; exact w18_54
  have w19_58 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m19]; exact w18_58
  have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m19]; exact w18_5c
  have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m19]; exact w18_60
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m19]; exact w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m19]; exact w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m19]; exact w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m19]; exact w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m19]; exact w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m19]; exact w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m19]; exact w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m19]; exact w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m19]; exact w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m19]; exact w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m19]; exact w18_8c
  have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m19]; exact w18_90
  have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m19]; exact w18_94
  have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m19]; exact w18_a20
  have w19_a24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m19]; exact w18_a24
  have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m19]; exact w18_a28
  have w19_a2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m19]; exact w18_a2c
  have w19_a30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m19]; exact w18_a30
  have w19_a34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m19]; exact w18_a34
  have w19_a38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m19]; exact w18_a38
  have w19_a3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m19]; exact w18_a3c
  have w19_a40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m19]; exact w18_a40
  have w19_a44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m19]; exact w18_a44
  clear w18_a44 w18_a40 w18_a3c w18_a38 w18_a34 w18_a30 w18_a2c w18_a28 w18_a24 w18_a20 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_34 w18_30 g18_11 g18_27 g18_26 g18_25 g18_21 g18_19 g18_18 g18_10 g18_9 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x9F6
  obtain ⟨n20, c20, u20⟩ := s19.block svL79f6 E19.self svL79f6_end
    ⟨trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x9F8 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svL79f6 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_9 : reg n20 (9 : Fin 32) = x9 := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_10 : reg n20 a0 = if BitVec.ult 0 (sl8) then (1 : Word) else 0 := by
    rw [rb20, runBlock_reg _ _ _ a0 s19.zero (by decide), g19_10]
  have g20_12 : reg n20 a2 = f34 := by
    rw [rb20, runBlock_reg _ _ _ a2 s19.zero (by decide), g19_12]
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_11 : reg n20 a1 = (f30) &&& (f34) := by
    rw [rb20, ← g19_11, ← g19_12]; rfl
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m20]; exact w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m20]; exact w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m20]; exact w19_38
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m20]; exact w19_3c
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m20]; exact w19_40
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m20]; exact w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m20]; exact w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m20]; exact w19_4c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
  have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m20]; exact w19_54
  have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m20]; exact w19_58
  have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m20]; exact w19_5c
  have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m20]; exact w19_60
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m20]; exact w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m20]; exact w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m20]; exact w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m20]; exact w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m20]; exact w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m20]; exact w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m20]; exact w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m20]; exact w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m20]; exact w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m20]; exact w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m20]; exact w19_8c
  have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m20]; exact w19_90
  have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m20]; exact w19_94
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
  clear w19_a44 w19_a40 w19_a3c w19_a38 w19_a34 w19_a30 w19_a2c w19_a28 w19_a24 w19_a20 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_34 w19_30 g19_12 g19_27 g19_26 g19_25 g19_21 g19_19 g19_18 g19_11 g19_10 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x9F8
  obtain ⟨n21, c21, u21⟩ := s20.block svL79f8 E20.self svL79f8_end
    ⟨trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x9FA (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svL79f8 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by
    rw [rb21, runBlock_reg _ _ _ sp s20.zero (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (3 : Fin 32) s20.zero (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (4 : Fin 32) s20.zero (by decide), g20_4]
  have g21_9 : reg n21 (9 : Fin 32) = x9 := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
  have g21_11 : reg n21 a1 = (f30) &&& (f34) := by
    rw [rb21, runBlock_reg _ _ _ a1 s20.zero (by decide), g20_11]
  have g21_12 : reg n21 a2 = f34 := by
    rw [rb21, runBlock_reg _ _ _ a2 s20.zero (by decide), g20_12]
  have g21_18 : reg n21 (18 : Fin 32) = out := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_10 : reg n21 a0 = (if BitVec.ult 0 (sl8) then (1 : Word) else 0) &&& ((f30) &&& (f34)) := by
    rw [rb21, ← g20_10, ← g20_11]; rfl
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m21]; exact w20_30
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m21]; exact w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m21]; exact w20_38
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m21]; exact w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m21]; exact w20_40
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m21]; exact w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m21]; exact w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m21]; exact w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m21]; exact w20_50
  have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m21]; exact w20_54
  have w21_58 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m21]; exact w20_58
  have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m21]; exact w20_5c
  have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m21]; exact w20_60
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m21]; exact w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m21]; exact w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m21]; exact w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m21]; exact w20_70
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m21]; exact w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m21]; exact w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m21]; exact w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m21]; exact w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m21]; exact w20_84
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m21]; exact w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m21]; exact w20_8c
  have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m21]; exact w20_90
  have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m21]; exact w20_94
  have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m21]; exact w20_a20
  have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m21]; exact w20_a24
  have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m21]; exact w20_a28
  have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m21]; exact w20_a2c
  have w21_a30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m21]; exact w20_a30
  have w21_a34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m21]; exact w20_a34
  have w21_a38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m21]; exact w20_a38
  have w21_a3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m21]; exact w20_a3c
  have w21_a40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m21]; exact w20_a40
  have w21_a44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m21]; exact w20_a44
  clear w20_a44 w20_a40 w20_a3c w20_a38 w20_a34 w20_a30 w20_a2c w20_a28 w20_a24 w20_a20 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_34 w20_30 g20_11 g20_27 g20_26 g20_25 g20_21 g20_19 g20_18 g20_12 g20_10 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  by_cases hz_21 : (if BitVec.ult 0 (sl8) then (1 : Word) else 0) &&& ((f30) &&& (f34)) ≠ 0
  rotate_left
  · -- 0x9FA: branch, taken
    obtain ⟨n22, d22, u22⟩ := s21.taken E21.self 0xB32 sv_at_9fa
      (by decide) (by rw [g21_10, s21.zero]; exact br_beq_t (Decidable.of_not_not hz_21))
    have s22 : St n22.mem SV n22 0xB32 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
    have g22_9 : reg n22 (9 : Fin 32) = x9 := by rw [u22.regs, g21_9]
    have g22_10 : reg n22 a0 = (if BitVec.ult 0 (sl8) then (1 : Word) else 0) &&& ((f30) &&& (f34)) := by rw [u22.regs, g21_10]
    have g22_11 : reg n22 a1 = (f30) &&& (f34) := by rw [u22.regs, g21_11]
    have g22_12 : reg n22 a2 = f34 := by rw [u22.regs, g21_12]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
    have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u22.regs, g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m22]; exact w21_30
    have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m22]; exact w21_34
    have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m22]; exact w21_38
    have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m22]; exact w21_3c
    have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m22]; exact w21_40
    have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m22]; exact w21_44
    have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m22]; exact w21_48
    have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m22]; exact w21_4c
    have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m22]; exact w21_50
    have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m22]; exact w21_54
    have w22_58 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m22]; exact w21_58
    have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m22]; exact w21_5c
    have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m22]; exact w21_60
    have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m22]; exact w21_64
    have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m22]; exact w21_68
    have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m22]; exact w21_6c
    have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m22]; exact w21_70
    have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m22]; exact w21_74
    have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m22]; exact w21_78
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m22]; exact w21_7c
    have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m22]; exact w21_80
    have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m22]; exact w21_84
    have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m22]; exact w21_88
    have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m22]; exact w21_8c
    have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m22]; exact w21_90
    have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m22]; exact w21_94
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
    clear w21_a44 w21_a40 w21_a3c w21_a38 w21_a34 w21_a30 w21_a2c w21_a28 w21_a24 w21_a20 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_34 w21_30 g21_10 g21_27 g21_26 g21_25 g21_21 g21_19 g21_18 g21_12 g21_11 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
    -- 0xB32
    obtain ⟨n23, c23, u23⟩ := s22.block svL7b32 E22.self svL7b32_end
      ⟨trivial, trivial⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have s23 : St n23.mem SV n23 0xB34 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have rb23 : ∀ q, reg n23 q = (runBlock svL7b32 (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
    have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
    have t23 : Steps n0 n23 := t22.trans c23
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.same m23
    have g23_2 : reg n23 sp = B + 0x21A0 := by
      rw [rb23, runBlock_reg _ _ _ sp s22.zero (by decide), g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb23, runBlock_reg _ _ _ (3 : Fin 32) s22.zero (by decide), g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb23, runBlock_reg _ _ _ (4 : Fin 32) s22.zero (by decide), g22_4]
    have g23_9 : reg n23 (9 : Fin 32) = x9 := by
      rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
    have g23_10 : reg n23 a0 = (if BitVec.ult 0 (sl8) then (1 : Word) else 0) &&& ((f30) &&& (f34)) := by
      rw [rb23, runBlock_reg _ _ _ a0 s22.zero (by decide), g22_10]
    have g23_11 : reg n23 a1 = (f30) &&& (f34) := by
      rw [rb23, runBlock_reg _ _ _ a1 s22.zero (by decide), g22_11]
    have g23_12 : reg n23 a2 = f34 := by
      rw [rb23, runBlock_reg _ _ _ a2 s22.zero (by decide), g22_12]
    have g23_18 : reg n23 (18 : Fin 32) = out := by
      rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by
      rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
    have g23_21 : reg n23 (21 : Fin 32) = x21 := by
      rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
    have g23_25 : reg n23 (25 : Fin 32) = x25 := by
      rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = x26 := by
      rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
    have g23_20 : reg n23 (20 : Fin 32) = BitVec.ofNat 32 0x16 := by
      rw [rb23]; simp +decide only [runBlock, BInstr.run, svL7b32, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g22_2, g22_3, g22_4, g22_9, g22_10, g22_11, g22_12, g22_18, g22_19, g22_21, g22_25, g22_26, g22_27, s22.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m23]; exact w22_30
    have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m23]; exact w22_34
    have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m23]; exact w22_38
    have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m23]; exact w22_3c
    have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m23]; exact w22_40
    have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m23]; exact w22_44
    have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m23]; exact w22_48
    have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m23]; exact w22_4c
    have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
    have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m23]; exact w22_54
    have w23_58 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m23]; exact w22_58
    have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m23]; exact w22_5c
    have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m23]; exact w22_60
    have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m23]; exact w22_64
    have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m23]; exact w22_68
    have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m23]; exact w22_6c
    have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m23]; exact w22_70
    have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m23]; exact w22_74
    have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m23]; exact w22_78
    have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m23]; exact w22_7c
    have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m23]; exact w22_80
    have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m23]; exact w22_84
    have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m23]; exact w22_88
    have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m23]; exact w22_8c
    have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m23]; exact w22_90
    have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m23]; exact w22_94
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
    clear w22_a44 w22_a40 w22_a3c w22_a38 w22_a34 w22_a30 w22_a2c w22_a28 w22_a24 w22_a20 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 g22_27 g22_26 g22_25 g22_21 g22_19 g22_18 g22_12 g22_11 g22_10 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    -- 0xB34: j
    obtain ⟨n24, d24, u24⟩ := s23.jump E23.self sv_at_b34 (off' := 0x966) (by decide)
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
    have g24_9 : reg n24 (9 : Fin 32) = x9 := by rw [u24.regs, g23_9]
    have g24_10 : reg n24 a0 = (if BitVec.ult 0 (sl8) then (1 : Word) else 0) &&& ((f30) &&& (f34)) := by rw [u24.regs, g23_10]
    have g24_11 : reg n24 a1 = (f30) &&& (f34) := by rw [u24.regs, g23_11]
    have g24_12 : reg n24 a2 = f34 := by rw [u24.regs, g23_12]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = BitVec.ofNat 32 0x16 := by rw [u24.regs, g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, g23_21]
    have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u24.regs, g23_27]
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m24]; exact w23_30
    have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m24]; exact w23_34
    have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m24]; exact w23_38
    have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m24]; exact w23_3c
    have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m24]; exact w23_40
    have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m24]; exact w23_44
    have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m24]; exact w23_48
    have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m24]; exact w23_4c
    have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
    have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m24]; exact w23_54
    have w24_58 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m24]; exact w23_58
    have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m24]; exact w23_5c
    have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m24]; exact w23_60
    have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m24]; exact w23_64
    have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m24]; exact w23_68
    have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m24]; exact w23_6c
    have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m24]; exact w23_70
    have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m24]; exact w23_74
    have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m24]; exact w23_78
    have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m24]; exact w23_7c
    have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m24]; exact w23_80
    have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m24]; exact w23_84
    have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m24]; exact w23_88
    have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m24]; exact w23_8c
    have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m24]; exact w23_90
    have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m24]; exact w23_94
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
    clear w23_a44 w23_a40 w23_a3c w23_a38 w23_a34 w23_a30 w23_a2c w23_a28 w23_a24 w23_a20 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 g23_20 g23_27 g23_26 g23_25 g23_21 g23_19 g23_18 g23_12 g23_11 g23_10 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
    exact .inl ⟨(fun ⟨h0', h1', h2', h3', h4', _⟩ => by exact hz_21 h4'), sv_fail F E24 s24 t24 (fun x hx => (fR24 x hx).trans (fM x hx).symm) V24 hret g24_2 g24_18 hO g24_3 g24_4⟩
  -- 0x9FA: branch, not taken
  obtain ⟨n22, d22, u22⟩ := s21.notTaken E21.self 0x9FE sv_at_9fa
    (by decide) (by rw [g21_10, s21.zero]; exact br_beq_f hz_21)
  have s22 : St n22.mem SV n22 0x9FE (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
  have g22_9 : reg n22 (9 : Fin 32) = x9 := by rw [u22.regs, g21_9]
  have g22_10 : reg n22 a0 = (if BitVec.ult 0 (sl8) then (1 : Word) else 0) &&& ((f30) &&& (f34)) := by rw [u22.regs, g21_10]
  have g22_11 : reg n22 a1 = (f30) &&& (f34) := by rw [u22.regs, g21_11]
  have g22_12 : reg n22 a2 = f34 := by rw [u22.regs, g21_12]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u22.regs, g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m22]; exact w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m22]; exact w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m22]; exact w21_38
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m22]; exact w21_3c
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m22]; exact w21_40
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m22]; exact w21_48
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m22]; exact w21_4c
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m22]; exact w21_50
  have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m22]; exact w21_54
  have w22_58 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m22]; exact w21_58
  have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m22]; exact w21_5c
  have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m22]; exact w21_60
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m22]; exact w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m22]; exact w21_68
  have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m22]; exact w21_6c
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m22]; exact w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m22]; exact w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m22]; exact w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m22]; exact w21_7c
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m22]; exact w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m22]; exact w21_84
  have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m22]; exact w21_88
  have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m22]; exact w21_8c
  have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m22]; exact w21_90
  have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m22]; exact w21_94
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
  clear w21_a44 w21_a40 w21_a3c w21_a38 w21_a34 w21_a30 w21_a2c w21_a28 w21_a24 w21_a20 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_34 w21_30 g21_10 g21_27 g21_26 g21_25 g21_21 g21_19 g21_18 g21_12 g21_11 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x9FE
  obtain ⟨n23, c23, u23⟩ := s22.block svL79fe E22.self svL79fe_end
    ⟨trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0xA00 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svL79fe (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans c23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by
    rw [rb23, runBlock_reg _ _ _ sp s22.zero (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (3 : Fin 32) s22.zero (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (4 : Fin 32) s22.zero (by decide), g22_4]
  have g23_9 : reg n23 (9 : Fin 32) = x9 := by
    rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
  have g23_10 : reg n23 a0 = (if BitVec.ult 0 (sl8) then (1 : Word) else 0) &&& ((f30) &&& (f34)) := by
    rw [rb23, runBlock_reg _ _ _ a0 s22.zero (by decide), g22_10]
  have g23_12 : reg n23 a2 = f34 := by
    rw [rb23, runBlock_reg _ _ _ a2 s22.zero (by decide), g22_12]
  have g23_18 : reg n23 (18 : Fin 32) = out := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_11 : reg n23 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svL79fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_9, g22_10, g22_11, g22_12, g22_18, g22_19, g22_21, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m23]; exact w22_38
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m23]; exact w22_3c
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m23]; exact w22_40
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m23]; exact w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m23]; exact w22_48
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m23]; exact w22_4c
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
  have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m23]; exact w22_54
  have w23_58 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m23]; exact w22_58
  have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m23]; exact w22_5c
  have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m23]; exact w22_60
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m23]; exact w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m23]; exact w22_68
  have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m23]; exact w22_6c
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m23]; exact w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m23]; exact w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m23]; exact w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m23]; exact w22_84
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m23]; exact w22_88
  have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m23]; exact w22_8c
  have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m23]; exact w22_90
  have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m23]; exact w22_94
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
  clear w22_a44 w22_a40 w22_a3c w22_a38 w22_a34 w22_a30 w22_a2c w22_a28 w22_a24 w22_a20 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 g22_27 g22_26 g22_25 g22_21 g22_19 g22_18 g22_12 g22_11 g22_10 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0xA00: lw
  obtain ⟨n24, d24, u24⟩ := s23.lw E23.self sv_at_a00 (off' := 0xA02) (by decide)
    (by rw [g23_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s24 : St n24.mem SV n24 0xA02 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_4]
  have g24_9 : reg n24 (9 : Fin 32) = x9 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_9]
  have g24_11 : reg n24 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_11]
  have g24_12 : reg n24 a2 = f34 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_12]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, upd_ne (by decide) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_19]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_21]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_27]
  have g24_10 : reg n24 a0 = sl1 := by
    rw [u24.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g23_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, w23_a24]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m24]; exact w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m24]; exact w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m24]; exact w23_38
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m24]; exact w23_3c
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m24]; exact w23_40
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m24]; exact w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m24]; exact w23_48
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m24]; exact w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
  have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m24]; exact w23_54
  have w24_58 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m24]; exact w23_58
  have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m24]; exact w23_5c
  have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m24]; exact w23_60
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m24]; exact w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m24]; exact w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m24]; exact w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m24]; exact w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m24]; exact w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m24]; exact w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m24]; exact w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m24]; exact w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m24]; exact w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m24]; exact w23_8c
  have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m24]; exact w23_90
  have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m24]; exact w23_94
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
  clear w23_a44 w23_a40 w23_a3c w23_a38 w23_a34 w23_a30 w23_a2c w23_a28 w23_a24 w23_a20 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 g23_11 g23_27 g23_26 g23_25 g23_21 g23_19 g23_18 g23_12 g23_10 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0xA02: sw
  obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_a02 (off' := 0xA04) (c := 0x34)
    (by decide) (by rw [g24_2]; sv_addr) (by decide) (by decide)
  have t25 : Steps n0 n25 := t24.trans d25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
  have g25_9 : reg n25 (9 : Fin 32) = x9 := by rw [rg25 (9 : Fin 32), g24_9]
  have g25_10 : reg n25 a0 = sl1 := by rw [rg25 a0, g24_10]
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg25 a1, g24_11]
  have g25_12 : reg n25 a2 = f34 := by rw [rg25 a2, g24_12]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rg25 (21 : Fin 32), g24_21]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rg25 (25 : Fin 32), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rg25 (26 : Fin 32), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg25 (27 : Fin 32), g24_27]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4)] := keep_kk24.trans K25.toL
  clear keep_kk24
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K25.w32 (by decide) (by decide)).trans w24_30
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := (K25.w32 (by decide) (by decide)).trans w24_38
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := (K25.w32 (by decide) (by decide)).trans w24_3c
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := (K25.w32 (by decide) (by decide)).trans w24_40
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := (K25.w32 (by decide) (by decide)).trans w24_44
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K25.w32 (by decide) (by decide)).trans w24_48
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K25.w32 (by decide) (by decide)).trans w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K25.w32 (by decide) (by decide)).trans w24_50
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K25.w32 (by decide) (by decide)).trans w24_54
  have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K25.w32 (by decide) (by decide)).trans w24_58
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K25.w32 (by decide) (by decide)).trans w24_5c
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K25.w32 (by decide) (by decide)).trans w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K25.w32 (by decide) (by decide)).trans w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K25.w32 (by decide) (by decide)).trans w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K25.w32 (by decide) (by decide)).trans w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K25.w32 (by decide) (by decide)).trans w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K25.w32 (by decide) (by decide)).trans w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K25.w32 (by decide) (by decide)).trans w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K25.w32 (by decide) (by decide)).trans w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K25.w32 (by decide) (by decide)).trans w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K25.w32 (by decide) (by decide)).trans w24_84
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K25.w32 (by decide) (by decide)).trans w24_88
  have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K25.w32 (by decide) (by decide)).trans w24_8c
  have w25_90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K25.w32 (by decide) (by decide)).trans w24_90
  have w25_94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K25.w32 (by decide) (by decide)).trans w24_94
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
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [W25, g24_10]
  clear w24_a44 w24_a40 w24_a3c w24_a38 w24_a34 w24_a30 w24_a2c w24_a28 w24_a24 w24_a20 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 g24_10 g24_27 g24_26 g24_25 g24_21 g24_19 g24_18 g24_12 g24_11 g24_9 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0xA04: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_a04 (off' := 0xA06) (by decide)
    (by rw [g25_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0xA06 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_9 : reg n26 (9 : Fin 32) = x9 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
  have g26_11 : reg n26 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_11]
  have g26_12 : reg n26 a2 = f34 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_12]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_10 : reg n26 a0 = sl3 := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr, w25_a2c]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m26]; exact w25_30
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m26]; exact w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m26]; exact w25_38
  have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m26]; exact w25_3c
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m26]; exact w25_40
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m26]; exact w25_44
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m26]; exact w25_48
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m26]; exact w25_4c
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m26]; exact w25_50
  have w26_54 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m26]; exact w25_54
  have w26_58 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m26]; exact w25_58
  have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m26]; exact w25_5c
  have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m26]; exact w25_60
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m26]; exact w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m26]; exact w25_68
  have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m26]; exact w25_6c
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m26]; exact w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m26]; exact w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m26]; exact w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m26]; exact w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m26]; exact w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m26]; exact w25_84
  have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m26]; exact w25_88
  have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m26]; exact w25_8c
  have w26_90 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m26]; exact w25_90
  have w26_94 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m26]; exact w25_94
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
  clear w25_34 w25_a44 w25_a40 w25_a3c w25_a38 w25_a34 w25_a30 w25_a2c w25_a28 w25_a24 w25_a20 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_44 w25_40 w25_3c w25_38 w25_30 g25_27 g25_26 g25_25 g25_21 g25_19 g25_18 g25_12 g25_11 g25_10 g25_9 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
  -- 0xA06: sw
  obtain ⟨n27, d27, s27, fr27, K27, W27, rg27⟩ := sv_sw F E26 s26 sv_at_a06 (off' := 0xA08) (c := 0x30)
    (by decide) (by rw [g26_2]; sv_addr) (by decide) (by decide)
  have t27 : Steps n0 n27 := t26.trans d27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keep K27 (by decide)
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rg27 sp, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg27 (3 : Fin 32), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg27 (4 : Fin 32), g26_4]
  have g27_9 : reg n27 (9 : Fin 32) = x9 := by rw [rg27 (9 : Fin 32), g26_9]
  have g27_10 : reg n27 a0 = sl3 := by rw [rg27 a0, g26_10]
  have g27_11 : reg n27 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg27 a1, g26_11]
  have g27_12 : reg n27 a2 = f34 := by rw [rg27 a2, g26_12]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rg27 (18 : Fin 32), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rg27 (19 : Fin 32), g26_19]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [rg27 (21 : Fin 32), g26_21]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [rg27 (25 : Fin 32), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [rg27 (26 : Fin 32), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg27 (27 : Fin 32), g26_27]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4)] := keep_kk26.trans K27.toL
  clear keep_kk26
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := (K27.w32 (by decide) (by decide)).trans w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := (K27.w32 (by decide) (by decide)).trans w26_38
  have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := (K27.w32 (by decide) (by decide)).trans w26_3c
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := (K27.w32 (by decide) (by decide)).trans w26_40
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := (K27.w32 (by decide) (by decide)).trans w26_44
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K27.w32 (by decide) (by decide)).trans w26_48
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K27.w32 (by decide) (by decide)).trans w26_4c
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K27.w32 (by decide) (by decide)).trans w26_50
  have w27_54 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K27.w32 (by decide) (by decide)).trans w26_54
  have w27_58 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K27.w32 (by decide) (by decide)).trans w26_58
  have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K27.w32 (by decide) (by decide)).trans w26_5c
  have w27_60 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K27.w32 (by decide) (by decide)).trans w26_60
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K27.w32 (by decide) (by decide)).trans w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K27.w32 (by decide) (by decide)).trans w26_68
  have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K27.w32 (by decide) (by decide)).trans w26_6c
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K27.w32 (by decide) (by decide)).trans w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K27.w32 (by decide) (by decide)).trans w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K27.w32 (by decide) (by decide)).trans w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K27.w32 (by decide) (by decide)).trans w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K27.w32 (by decide) (by decide)).trans w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K27.w32 (by decide) (by decide)).trans w26_84
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K27.w32 (by decide) (by decide)).trans w26_88
  have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K27.w32 (by decide) (by decide)).trans w26_8c
  have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K27.w32 (by decide) (by decide)).trans w26_90
  have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K27.w32 (by decide) (by decide)).trans w26_94
  have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K27.w32 (by decide) (by decide)).trans w26_a20
  have w27_a24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K27.w32 (by decide) (by decide)).trans w26_a24
  have w27_a28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K27.w32 (by decide) (by decide)).trans w26_a28
  have w27_a2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K27.w32 (by decide) (by decide)).trans w26_a2c
  have w27_a30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K27.w32 (by decide) (by decide)).trans w26_a30
  have w27_a34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K27.w32 (by decide) (by decide)).trans w26_a34
  have w27_a38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K27.w32 (by decide) (by decide)).trans w26_a38
  have w27_a3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K27.w32 (by decide) (by decide)).trans w26_a3c
  have w27_a40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K27.w32 (by decide) (by decide)).trans w26_a40
  have w27_a44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K27.w32 (by decide) (by decide)).trans w26_a44
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [W27, g26_10]
  clear w26_a44 w26_a40 w26_a3c w26_a38 w26_a34 w26_a30 w26_a2c w26_a28 w26_a24 w26_a20 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 g26_10 g26_27 g26_26 g26_25 g26_21 g26_19 g26_18 g26_12 g26_11 g26_9 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0xA08: lw
  obtain ⟨n28, d28, u28⟩ := s27.lw E27.self sv_at_a08 (off' := 0xA0A) (by decide)
    (by rw [g27_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x14 = B + 0x21A0 + BitVec.ofNat 32 0xA34 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s28 : St n28.mem SV n28 0xA0A (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_4]
  have g28_9 : reg n28 (9 : Fin 32) = x9 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_9]
  have g28_11 : reg n28 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_11]
  have g28_12 : reg n28 a2 = f34 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_12]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, upd_ne (by decide) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_19]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_21]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_27]
  have g28_10 : reg n28 a0 = sl5 := by
    rw [u28.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g27_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x14 = B + 0x21A0 + BitVec.ofNat 32 0xA34 by sv_addr, w27_a34]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m28]; exact w27_30
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m28]; exact w27_34
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m28]; exact w27_38
  have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m28]; exact w27_3c
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m28]; exact w27_40
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m28]; exact w27_44
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m28]; exact w27_48
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m28]; exact w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m28]; exact w27_50
  have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m28]; exact w27_54
  have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m28]; exact w27_58
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m28]; exact w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m28]; exact w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m28]; exact w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m28]; exact w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m28]; exact w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m28]; exact w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m28]; exact w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m28]; exact w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m28]; exact w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m28]; exact w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m28]; exact w27_84
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m28]; exact w27_88
  have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m28]; exact w27_8c
  have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m28]; exact w27_90
  have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m28]; exact w27_94
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
  clear w27_30 w27_a44 w27_a40 w27_a3c w27_a38 w27_a34 w27_a30 w27_a2c w27_a28 w27_a24 w27_a20 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_44 w27_40 w27_3c w27_38 w27_34 g27_27 g27_26 g27_25 g27_21 g27_19 g27_18 g27_12 g27_11 g27_10 g27_9 g27_4 g27_3 g27_2 V27 E27 fR27 t27 rg27 W27 K27 fr27 s27 d27
  -- 0xA0A: sw
  obtain ⟨n29, d29, s29, fr29, K29, W29, rg29⟩ := sv_sw F E28 s28 sv_at_a0a (off' := 0xA0C) (c := 0x2C)
    (by decide) (by rw [g28_2]; sv_addr) (by decide) (by decide)
  have t29 : Steps n0 n29 := t28.trans d29
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.keep K29 (by decide)
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [rg29 sp, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg29 (3 : Fin 32), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg29 (4 : Fin 32), g28_4]
  have g29_9 : reg n29 (9 : Fin 32) = x9 := by rw [rg29 (9 : Fin 32), g28_9]
  have g29_10 : reg n29 a0 = sl5 := by rw [rg29 a0, g28_10]
  have g29_11 : reg n29 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg29 a1, g28_11]
  have g29_12 : reg n29 a2 = f34 := by rw [rg29 a2, g28_12]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [rg29 (18 : Fin 32), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [rg29 (19 : Fin 32), g28_19]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [rg29 (21 : Fin 32), g28_21]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [rg29 (25 : Fin 32), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [rg29 (26 : Fin 32), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg29 (27 : Fin 32), g28_27]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4)] := keep_kk28.trans K29.toL
  clear keep_kk28
  have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := (K29.w32 (by decide) (by decide)).trans w28_30
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := (K29.w32 (by decide) (by decide)).trans w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := (K29.w32 (by decide) (by decide)).trans w28_38
  have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := (K29.w32 (by decide) (by decide)).trans w28_3c
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := (K29.w32 (by decide) (by decide)).trans w28_40
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := (K29.w32 (by decide) (by decide)).trans w28_44
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K29.w32 (by decide) (by decide)).trans w28_48
  have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K29.w32 (by decide) (by decide)).trans w28_4c
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K29.w32 (by decide) (by decide)).trans w28_50
  have w29_54 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K29.w32 (by decide) (by decide)).trans w28_54
  have w29_58 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K29.w32 (by decide) (by decide)).trans w28_58
  have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K29.w32 (by decide) (by decide)).trans w28_5c
  have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K29.w32 (by decide) (by decide)).trans w28_60
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K29.w32 (by decide) (by decide)).trans w28_64
  have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K29.w32 (by decide) (by decide)).trans w28_68
  have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K29.w32 (by decide) (by decide)).trans w28_6c
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K29.w32 (by decide) (by decide)).trans w28_70
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K29.w32 (by decide) (by decide)).trans w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K29.w32 (by decide) (by decide)).trans w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K29.w32 (by decide) (by decide)).trans w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K29.w32 (by decide) (by decide)).trans w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K29.w32 (by decide) (by decide)).trans w28_84
  have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K29.w32 (by decide) (by decide)).trans w28_88
  have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K29.w32 (by decide) (by decide)).trans w28_8c
  have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K29.w32 (by decide) (by decide)).trans w28_90
  have w29_94 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K29.w32 (by decide) (by decide)).trans w28_94
  have w29_a20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K29.w32 (by decide) (by decide)).trans w28_a20
  have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K29.w32 (by decide) (by decide)).trans w28_a24
  have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K29.w32 (by decide) (by decide)).trans w28_a28
  have w29_a2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K29.w32 (by decide) (by decide)).trans w28_a2c
  have w29_a30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K29.w32 (by decide) (by decide)).trans w28_a30
  have w29_a34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K29.w32 (by decide) (by decide)).trans w28_a34
  have w29_a38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K29.w32 (by decide) (by decide)).trans w28_a38
  have w29_a3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K29.w32 (by decide) (by decide)).trans w28_a3c
  have w29_a40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K29.w32 (by decide) (by decide)).trans w28_a40
  have w29_a44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K29.w32 (by decide) (by decide)).trans w28_a44
  have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [W29, g28_10]
  clear w28_a44 w28_a40 w28_a3c w28_a38 w28_a34 w28_a30 w28_a2c w28_a28 w28_a24 w28_a20 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 g28_10 g28_27 g28_26 g28_25 g28_21 g28_19 g28_18 g28_12 g28_11 g28_9 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  -- 0xA0C: lw
  obtain ⟨n30, d30, u30⟩ := s29.lw E29.self sv_at_a0c (off' := 0xA0E) (by decide)
    (by rw [g29_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x1C = B + 0x21A0 + BitVec.ofNat 32 0xA3C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s30 : St n30.mem SV n30 0xA0E (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_4]
  have g30_9 : reg n30 (9 : Fin 32) = x9 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_9]
  have g30_11 : reg n30 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_11]
  have g30_12 : reg n30 a2 = f34 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_12]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, upd_ne (by decide) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_19]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_21]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_27]
  have g30_10 : reg n30 a0 = sl7 := by
    rw [u30.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g29_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x1C = B + 0x21A0 + BitVec.ofNat 32 0xA3C by sv_addr, w29_a3c]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m30]; exact w29_2c
  have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m30]; exact w29_30
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m30]; exact w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m30]; exact w29_38
  have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m30]; exact w29_3c
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m30]; exact w29_40
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m30]; exact w29_44
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m30]; exact w29_48
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m30]; exact w29_4c
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m30]; exact w29_50
  have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m30]; exact w29_54
  have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m30]; exact w29_58
  have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m30]; exact w29_5c
  have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m30]; exact w29_60
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m30]; exact w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m30]; exact w29_68
  have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m30]; exact w29_6c
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m30]; exact w29_70
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m30]; exact w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m30]; exact w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m30]; exact w29_7c
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m30]; exact w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m30]; exact w29_84
  have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m30]; exact w29_88
  have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m30]; exact w29_8c
  have w30_90 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m30]; exact w29_90
  have w30_94 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m30]; exact w29_94
  have w30_a20 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m30]; exact w29_a20
  have w30_a24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m30]; exact w29_a24
  have w30_a28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m30]; exact w29_a28
  have w30_a2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m30]; exact w29_a2c
  have w30_a30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m30]; exact w29_a30
  have w30_a34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m30]; exact w29_a34
  have w30_a38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m30]; exact w29_a38
  have w30_a3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m30]; exact w29_a3c
  have w30_a40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m30]; exact w29_a40
  have w30_a44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m30]; exact w29_a44
  clear w29_2c w29_a44 w29_a40 w29_a3c w29_a38 w29_a34 w29_a30 w29_a2c w29_a28 w29_a24 w29_a20 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_44 w29_40 w29_3c w29_38 w29_34 w29_30 g29_27 g29_26 g29_25 g29_21 g29_19 g29_18 g29_12 g29_11 g29_10 g29_9 g29_4 g29_3 g29_2 V29 E29 fR29 t29 rg29 W29 K29 fr29 s29 d29
  -- 0xA0E: sw
  obtain ⟨n31, d31, s31, fr31, K31, W31, rg31⟩ := sv_sw F E30 s30 sv_at_a0e (off' := 0xA10) (c := 0x28)
    (by decide) (by rw [g30_2]; sv_addr) (by decide) (by decide)
  have t31 : Steps n0 n31 := t30.trans d31
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.keep K31 (by decide)
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [rg31 sp, g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg31 (3 : Fin 32), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg31 (4 : Fin 32), g30_4]
  have g31_9 : reg n31 (9 : Fin 32) = x9 := by rw [rg31 (9 : Fin 32), g30_9]
  have g31_10 : reg n31 a0 = sl7 := by rw [rg31 a0, g30_10]
  have g31_11 : reg n31 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg31 a1, g30_11]
  have g31_12 : reg n31 a2 = f34 := by rw [rg31 a2, g30_12]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [rg31 (18 : Fin 32), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [rg31 (19 : Fin 32), g30_19]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [rg31 (21 : Fin 32), g30_21]
  have g31_25 : reg n31 (25 : Fin 32) = x25 := by rw [rg31 (25 : Fin 32), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [rg31 (26 : Fin 32), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg31 (27 : Fin 32), g30_27]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4)] := keep_kk30.trans K31.toL
  clear keep_kk30
  have w31_2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := (K31.w32 (by decide) (by decide)).trans w30_2c
  have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := (K31.w32 (by decide) (by decide)).trans w30_30
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := (K31.w32 (by decide) (by decide)).trans w30_34
  have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := (K31.w32 (by decide) (by decide)).trans w30_38
  have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := (K31.w32 (by decide) (by decide)).trans w30_3c
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := (K31.w32 (by decide) (by decide)).trans w30_40
  have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := (K31.w32 (by decide) (by decide)).trans w30_44
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K31.w32 (by decide) (by decide)).trans w30_48
  have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K31.w32 (by decide) (by decide)).trans w30_4c
  have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K31.w32 (by decide) (by decide)).trans w30_50
  have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K31.w32 (by decide) (by decide)).trans w30_54
  have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K31.w32 (by decide) (by decide)).trans w30_58
  have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K31.w32 (by decide) (by decide)).trans w30_5c
  have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K31.w32 (by decide) (by decide)).trans w30_60
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K31.w32 (by decide) (by decide)).trans w30_64
  have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K31.w32 (by decide) (by decide)).trans w30_68
  have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K31.w32 (by decide) (by decide)).trans w30_6c
  have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K31.w32 (by decide) (by decide)).trans w30_70
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K31.w32 (by decide) (by decide)).trans w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K31.w32 (by decide) (by decide)).trans w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K31.w32 (by decide) (by decide)).trans w30_7c
  have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K31.w32 (by decide) (by decide)).trans w30_80
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K31.w32 (by decide) (by decide)).trans w30_84
  have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K31.w32 (by decide) (by decide)).trans w30_88
  have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K31.w32 (by decide) (by decide)).trans w30_8c
  have w31_90 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K31.w32 (by decide) (by decide)).trans w30_90
  have w31_94 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K31.w32 (by decide) (by decide)).trans w30_94
  have w31_a20 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K31.w32 (by decide) (by decide)).trans w30_a20
  have w31_a24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K31.w32 (by decide) (by decide)).trans w30_a24
  have w31_a28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K31.w32 (by decide) (by decide)).trans w30_a28
  have w31_a2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K31.w32 (by decide) (by decide)).trans w30_a2c
  have w31_a30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K31.w32 (by decide) (by decide)).trans w30_a30
  have w31_a34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K31.w32 (by decide) (by decide)).trans w30_a34
  have w31_a38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K31.w32 (by decide) (by decide)).trans w30_a38
  have w31_a3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K31.w32 (by decide) (by decide)).trans w30_a3c
  have w31_a40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K31.w32 (by decide) (by decide)).trans w30_a40
  have w31_a44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K31.w32 (by decide) (by decide)).trans w30_a44
  have w31_28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [W31, g30_10]
  clear w30_a44 w30_a40 w30_a3c w30_a38 w30_a34 w30_a30 w30_a2c w30_a28 w30_a24 w30_a20 w30_94 w30_90 w30_8c w30_88 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_48 w30_44 w30_40 w30_3c w30_38 w30_34 w30_30 w30_2c g30_10 g30_27 g30_26 g30_25 g30_21 g30_19 g30_18 g30_12 g30_11 g30_9 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
  -- 0xA10: lw
  obtain ⟨n32, d32, u32⟩ := s31.lw E31.self sv_at_a10 (off' := 0xA12) (by decide)
    (by rw [g31_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0xA44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s32 : St n32.mem SV n32 0xA12 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
  have g32_9 : reg n32 (9 : Fin 32) = x9 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
  have g32_11 : reg n32 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_11]
  have g32_12 : reg n32 a2 = f34 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_12]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
  have g32_25 : reg n32 (25 : Fin 32) = x25 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
  have g32_10 : reg n32 a0 = sl9 := by
    rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g31_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0xA44 by sv_addr, w31_a44]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m32]; exact w31_28
  have w32_2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m32]; exact w31_2c
  have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m32]; exact w31_30
  have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m32]; exact w31_34
  have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m32]; exact w31_38
  have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m32]; exact w31_3c
  have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m32]; exact w31_40
  have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m32]; exact w31_44
  have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m32]; exact w31_48
  have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m32]; exact w31_4c
  have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m32]; exact w31_50
  have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m32]; exact w31_54
  have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m32]; exact w31_58
  have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m32]; exact w31_5c
  have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m32]; exact w31_60
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m32]; exact w31_64
  have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m32]; exact w31_68
  have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m32]; exact w31_6c
  have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m32]; exact w31_70
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m32]; exact w31_74
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m32]; exact w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m32]; exact w31_7c
  have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m32]; exact w31_80
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m32]; exact w31_84
  have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m32]; exact w31_88
  have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m32]; exact w31_8c
  have w32_90 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m32]; exact w31_90
  have w32_94 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m32]; exact w31_94
  have w32_a20 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m32]; exact w31_a20
  have w32_a24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m32]; exact w31_a24
  have w32_a28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m32]; exact w31_a28
  have w32_a2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m32]; exact w31_a2c
  have w32_a30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m32]; exact w31_a30
  have w32_a34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m32]; exact w31_a34
  have w32_a38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m32]; exact w31_a38
  have w32_a3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m32]; exact w31_a3c
  have w32_a40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m32]; exact w31_a40
  have w32_a44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m32]; exact w31_a44
  clear w31_28 w31_a44 w31_a40 w31_a3c w31_a38 w31_a34 w31_a30 w31_a2c w31_a28 w31_a24 w31_a20 w31_94 w31_90 w31_8c w31_88 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_48 w31_44 w31_40 w31_3c w31_38 w31_34 w31_30 w31_2c g31_27 g31_26 g31_25 g31_21 g31_19 g31_18 g31_12 g31_11 g31_10 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 rg31 W31 K31 fr31 s31 d31
  -- 0xA12: sw
  obtain ⟨n33, d33, s33, fr33, K33, W33, rg33⟩ := sv_sw F E32 s32 sv_at_a12 (off' := 0xA14) (c := 0x24)
    (by decide) (by rw [g32_2]; sv_addr) (by decide) (by decide)
  have t33 : Steps n0 n33 := t32.trans d33
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.keep K33 (by decide)
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [rg33 sp, g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg33 (3 : Fin 32), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg33 (4 : Fin 32), g32_4]
  have g33_9 : reg n33 (9 : Fin 32) = x9 := by rw [rg33 (9 : Fin 32), g32_9]
  have g33_10 : reg n33 a0 = sl9 := by rw [rg33 a0, g32_10]
  have g33_11 : reg n33 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg33 a1, g32_11]
  have g33_12 : reg n33 a2 = f34 := by rw [rg33 a2, g32_12]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [rg33 (18 : Fin 32), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [rg33 (19 : Fin 32), g32_19]
  have g33_21 : reg n33 (21 : Fin 32) = x21 := by rw [rg33 (21 : Fin 32), g32_21]
  have g33_25 : reg n33 (25 : Fin 32) = x25 := by rw [rg33 (25 : Fin 32), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [rg33 (26 : Fin 32), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg33 (27 : Fin 32), g32_27]
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4)] := keep_kk32.trans K33.toL
  clear keep_kk32
  have w33_28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := (K33.w32 (by decide) (by decide)).trans w32_28
  have w33_2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := (K33.w32 (by decide) (by decide)).trans w32_2c
  have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := (K33.w32 (by decide) (by decide)).trans w32_30
  have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := (K33.w32 (by decide) (by decide)).trans w32_34
  have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := (K33.w32 (by decide) (by decide)).trans w32_38
  have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := (K33.w32 (by decide) (by decide)).trans w32_3c
  have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := (K33.w32 (by decide) (by decide)).trans w32_40
  have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := (K33.w32 (by decide) (by decide)).trans w32_44
  have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K33.w32 (by decide) (by decide)).trans w32_48
  have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K33.w32 (by decide) (by decide)).trans w32_4c
  have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K33.w32 (by decide) (by decide)).trans w32_50
  have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K33.w32 (by decide) (by decide)).trans w32_54
  have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K33.w32 (by decide) (by decide)).trans w32_58
  have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K33.w32 (by decide) (by decide)).trans w32_5c
  have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K33.w32 (by decide) (by decide)).trans w32_60
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K33.w32 (by decide) (by decide)).trans w32_64
  have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K33.w32 (by decide) (by decide)).trans w32_68
  have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K33.w32 (by decide) (by decide)).trans w32_6c
  have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K33.w32 (by decide) (by decide)).trans w32_70
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K33.w32 (by decide) (by decide)).trans w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K33.w32 (by decide) (by decide)).trans w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K33.w32 (by decide) (by decide)).trans w32_7c
  have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K33.w32 (by decide) (by decide)).trans w32_80
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K33.w32 (by decide) (by decide)).trans w32_84
  have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K33.w32 (by decide) (by decide)).trans w32_88
  have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K33.w32 (by decide) (by decide)).trans w32_8c
  have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K33.w32 (by decide) (by decide)).trans w32_90
  have w33_94 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K33.w32 (by decide) (by decide)).trans w32_94
  have w33_a20 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K33.w32 (by decide) (by decide)).trans w32_a20
  have w33_a24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K33.w32 (by decide) (by decide)).trans w32_a24
  have w33_a28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K33.w32 (by decide) (by decide)).trans w32_a28
  have w33_a2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K33.w32 (by decide) (by decide)).trans w32_a2c
  have w33_a30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K33.w32 (by decide) (by decide)).trans w32_a30
  have w33_a34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K33.w32 (by decide) (by decide)).trans w32_a34
  have w33_a38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K33.w32 (by decide) (by decide)).trans w32_a38
  have w33_a3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K33.w32 (by decide) (by decide)).trans w32_a3c
  have w33_a40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K33.w32 (by decide) (by decide)).trans w32_a40
  have w33_a44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K33.w32 (by decide) (by decide)).trans w32_a44
  have w33_24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [W33, g32_10]
  clear w32_a44 w32_a40 w32_a3c w32_a38 w32_a34 w32_a30 w32_a2c w32_a28 w32_a24 w32_a20 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_48 w32_44 w32_40 w32_3c w32_38 w32_34 w32_30 w32_2c w32_28 g32_10 g32_27 g32_26 g32_25 g32_21 g32_19 g32_18 g32_12 g32_11 g32_9 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0xA14: lw
  obtain ⟨n34, d34, u34⟩ := s33.lw E33.self sv_at_a14 (off' := 0xA16) (by decide)
    (by rw [g33_2, show B + 0x21A0 + 0x60 = B + 0x21A0 + BitVec.ofNat 32 0x60 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s34 : St n34.mem SV n34 0xA16 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans (.single d34)
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
  have g34_9 : reg n34 (9 : Fin 32) = x9 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_9]
  have g34_11 : reg n34 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_11]
  have g34_12 : reg n34 a2 = f34 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_12]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, upd_ne (by decide) (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_19]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_21]
  have g34_25 : reg n34 (25 : Fin 32) = x25 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_27]
  have g34_10 : reg n34 a0 = orp := by
    rw [u34.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g33_2, show B + 0x21A0 + 0x60 = B + 0x21A0 + BitVec.ofNat 32 0x60 by sv_addr, w33_60]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m34]; exact w33_24
  have w34_28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m34]; exact w33_28
  have w34_2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m34]; exact w33_2c
  have w34_30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m34]; exact w33_30
  have w34_34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m34]; exact w33_34
  have w34_38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m34]; exact w33_38
  have w34_3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m34]; exact w33_3c
  have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m34]; exact w33_40
  have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m34]; exact w33_44
  have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m34]; exact w33_48
  have w34_4c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m34]; exact w33_4c
  have w34_50 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m34]; exact w33_50
  have w34_54 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m34]; exact w33_54
  have w34_58 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m34]; exact w33_58
  have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m34]; exact w33_5c
  have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m34]; exact w33_60
  have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m34]; exact w33_64
  have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m34]; exact w33_68
  have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m34]; exact w33_6c
  have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m34]; exact w33_70
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m34]; exact w33_74
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m34]; exact w33_78
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m34]; exact w33_7c
  have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m34]; exact w33_80
  have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m34]; exact w33_84
  have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m34]; exact w33_88
  have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m34]; exact w33_8c
  have w34_90 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m34]; exact w33_90
  have w34_94 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m34]; exact w33_94
  have w34_a20 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m34]; exact w33_a20
  have w34_a24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m34]; exact w33_a24
  have w34_a28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m34]; exact w33_a28
  have w34_a2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m34]; exact w33_a2c
  have w34_a30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m34]; exact w33_a30
  have w34_a34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m34]; exact w33_a34
  have w34_a38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m34]; exact w33_a38
  have w34_a3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m34]; exact w33_a3c
  have w34_a40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m34]; exact w33_a40
  have w34_a44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m34]; exact w33_a44
  clear w33_24 w33_a44 w33_a40 w33_a3c w33_a38 w33_a34 w33_a30 w33_a2c w33_a28 w33_a24 w33_a20 w33_94 w33_90 w33_8c w33_88 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_48 w33_44 w33_40 w33_3c w33_38 w33_34 w33_30 w33_2c w33_28 g33_27 g33_26 g33_25 g33_21 g33_19 g33_18 g33_12 g33_11 g33_10 g33_9 g33_4 g33_3 g33_2 V33 E33 fR33 t33 rg33 W33 K33 fr33 s33 d33
  -- 0xA16: lw
  obtain ⟨n35, d35, u35⟩ := s34.lw E34.self sv_at_a16 (off' := 0xA18) (by decide)
    (by rw [g34_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s35 : St n35.mem SV n35 0xA18 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans (.single d35)
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_4]
  have g35_9 : reg n35 (9 : Fin 32) = x9 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_9]
  have g35_10 : reg n35 a0 = orp := by rw [u35.regs, upd_ne (by decide) (by decide), g34_10]
  have g35_12 : reg n35 a2 = f34 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_12]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, upd_ne (by decide) (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, upd_ne (by decide) (by decide), g34_19]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_21]
  have g35_25 : reg n35 (25 : Fin 32) = x25 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_27]
  have g35_11 : reg n35 a1 = BitVec.ofNat 32 orl := by
    rw [u35.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g34_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr, w34_64]
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m35]; exact w34_24
  have w35_28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m35]; exact w34_28
  have w35_2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m35]; exact w34_2c
  have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m35]; exact w34_30
  have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m35]; exact w34_34
  have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m35]; exact w34_38
  have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m35]; exact w34_3c
  have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m35]; exact w34_40
  have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m35]; exact w34_44
  have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m35]; exact w34_48
  have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m35]; exact w34_4c
  have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m35]; exact w34_50
  have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m35]; exact w34_54
  have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m35]; exact w34_58
  have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m35]; exact w34_5c
  have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m35]; exact w34_60
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m35]; exact w34_64
  have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m35]; exact w34_68
  have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m35]; exact w34_6c
  have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m35]; exact w34_70
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m35]; exact w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m35]; exact w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m35]; exact w34_7c
  have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m35]; exact w34_80
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m35]; exact w34_84
  have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m35]; exact w34_88
  have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m35]; exact w34_8c
  have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m35]; exact w34_90
  have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m35]; exact w34_94
  have w35_a20 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m35]; exact w34_a20
  have w35_a24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m35]; exact w34_a24
  have w35_a28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m35]; exact w34_a28
  have w35_a2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m35]; exact w34_a2c
  have w35_a30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m35]; exact w34_a30
  have w35_a34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m35]; exact w34_a34
  have w35_a38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m35]; exact w34_a38
  have w35_a3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m35]; exact w34_a3c
  have w35_a40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m35]; exact w34_a40
  have w35_a44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m35]; exact w34_a44
  clear w34_a44 w34_a40 w34_a3c w34_a38 w34_a34 w34_a30 w34_a2c w34_a28 w34_a24 w34_a20 w34_94 w34_90 w34_8c w34_88 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_44 w34_40 w34_3c w34_38 w34_34 w34_30 w34_2c w34_28 w34_24 g34_10 g34_27 g34_26 g34_25 g34_21 g34_19 g34_18 g34_12 g34_11 g34_9 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
  -- 0xA18: lw
  obtain ⟨n36, d36, u36⟩ := s35.lw E35.self sv_at_a18 (off' := 0xA1A) (by decide)
    (by rw [g35_2, show B + 0x21A0 + 0x70 = B + 0x21A0 + BitVec.ofNat 32 0x70 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s36 : St n36.mem SV n36 0xA1A (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
  have g36_9 : reg n36 (9 : Fin 32) = x9 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
  have g36_10 : reg n36 a0 = orp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_10]
  have g36_11 : reg n36 a1 = BitVec.ofNat 32 orl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_11]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
  have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
  have g36_25 : reg n36 (25 : Fin 32) = x25 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
  have g36_12 : reg n36 a2 = arp := by
    rw [u36.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g35_2, show B + 0x21A0 + 0x70 = B + 0x21A0 + BitVec.ofNat 32 0x70 by sv_addr, w35_70]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m36]; exact w35_24
  have w36_28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m36]; exact w35_28
  have w36_2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m36]; exact w35_2c
  have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m36]; exact w35_30
  have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m36]; exact w35_34
  have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m36]; exact w35_38
  have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m36]; exact w35_3c
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m36]; exact w35_40
  have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m36]; exact w35_44
  have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m36]; exact w35_48
  have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m36]; exact w35_4c
  have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m36]; exact w35_50
  have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m36]; exact w35_54
  have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m36]; exact w35_58
  have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m36]; exact w35_5c
  have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m36]; exact w35_60
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m36]; exact w35_64
  have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m36]; exact w35_68
  have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m36]; exact w35_6c
  have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m36]; exact w35_70
  have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m36]; exact w35_74
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m36]; exact w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m36]; exact w35_7c
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m36]; exact w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m36]; exact w35_84
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m36]; exact w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m36]; exact w35_8c
  have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m36]; exact w35_90
  have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m36]; exact w35_94
  have w36_a20 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m36]; exact w35_a20
  have w36_a24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m36]; exact w35_a24
  have w36_a28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m36]; exact w35_a28
  have w36_a2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m36]; exact w35_a2c
  have w36_a30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m36]; exact w35_a30
  have w36_a34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m36]; exact w35_a34
  have w36_a38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m36]; exact w35_a38
  have w36_a3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m36]; exact w35_a3c
  have w36_a40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m36]; exact w35_a40
  have w36_a44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m36]; exact w35_a44
  clear w35_a44 w35_a40 w35_a3c w35_a38 w35_a34 w35_a30 w35_a2c w35_a28 w35_a24 w35_a20 w35_94 w35_90 w35_8c w35_88 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_44 w35_40 w35_3c w35_38 w35_34 w35_30 w35_2c w35_28 w35_24 g35_11 g35_27 g35_26 g35_25 g35_21 g35_19 g35_18 g35_12 g35_10 g35_9 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
  -- 0xA1A: lw
  obtain ⟨n37, d37, u37⟩ := s36.lw E36.self sv_at_a1a (off' := 0xA1C) (by decide)
    (by rw [g36_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s37 : St n37.mem SV n37 0xA1C (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans (.single d37)
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_4]
  have g37_9 : reg n37 (9 : Fin 32) = x9 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_9]
  have g37_10 : reg n37 a0 = orp := by rw [u37.regs, upd_ne (by decide) (by decide), g36_10]
  have g37_11 : reg n37 a1 = BitVec.ofNat 32 orl := by rw [u37.regs, upd_ne (by decide) (by decide), g36_11]
  have g37_12 : reg n37 a2 = arp := by rw [u37.regs, upd_ne (by decide) (by decide), g36_12]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, upd_ne (by decide) (by decide), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, upd_ne (by decide) (by decide), g36_19]
  have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_21]
  have g37_25 : reg n37 (25 : Fin 32) = x25 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_27]
  have g37_13 : reg n37 a3 = BitVec.ofNat 32 arl := by
    rw [u37.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g36_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr, w36_74]
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4)] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have w37_24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m37]; exact w36_24
  have w37_28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m37]; exact w36_28
  have w37_2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m37]; exact w36_2c
  have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m37]; exact w36_30
  have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m37]; exact w36_34
  have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m37]; exact w36_38
  have w37_3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m37]; exact w36_3c
  have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m37]; exact w36_40
  have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m37]; exact w36_44
  have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m37]; exact w36_48
  have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m37]; exact w36_4c
  have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m37]; exact w36_50
  have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m37]; exact w36_54
  have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m37]; exact w36_58
  have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m37]; exact w36_5c
  have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m37]; exact w36_60
  have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m37]; exact w36_64
  have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m37]; exact w36_68
  have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m37]; exact w36_6c
  have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m37]; exact w36_70
  have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m37]; exact w36_74
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m37]; exact w36_78
  have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m37]; exact w36_7c
  have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m37]; exact w36_80
  have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m37]; exact w36_84
  have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m37]; exact w36_88
  have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m37]; exact w36_8c
  have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m37]; exact w36_90
  have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m37]; exact w36_94
  have w37_a20 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m37]; exact w36_a20
  have w37_a24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m37]; exact w36_a24
  have w37_a28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m37]; exact w36_a28
  have w37_a2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m37]; exact w36_a2c
  have w37_a30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m37]; exact w36_a30
  have w37_a34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m37]; exact w36_a34
  have w37_a38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m37]; exact w36_a38
  have w37_a3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m37]; exact w36_a3c
  have w37_a40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m37]; exact w36_a40
  have w37_a44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m37]; exact w36_a44
  clear w36_a44 w36_a40 w36_a3c w36_a38 w36_a34 w36_a30 w36_a2c w36_a28 w36_a24 w36_a20 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_44 w36_40 w36_3c w36_38 w36_34 w36_30 w36_2c w36_28 w36_24 g36_12 g36_27 g36_26 g36_25 g36_21 g36_19 g36_18 g36_11 g36_10 g36_9 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
  -- 0xA1C: sv_sneF
  obtain ⟨n38, c38, s38, rk38, a0_38, K38, fr38⟩ := sv_sneF (pl := orl) (ql := arl)
    F E37 s37 sv_at_a1c sv_at_a20 (by decide) (by decide) g37_2
    g37_10 g37_11 g37_12 g37_13 (.inl or_in) (.inl ar_in)
  have t38 : Steps n0 n38 := t37.trans c38
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.keepL K38 (by decide)
  rw [sv_mbRo F fR37 (.inl or_in), sv_mbRo F fR37 (.inl ar_in)] at a0_38
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [rk38 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk38 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk38 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g37_4]
  have g38_9 : reg n38 (9 : Fin 32) = x9 := by rw [rk38 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g37_9]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [rk38 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [rk38 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g37_19]
  have g38_21 : reg n38 (21 : Fin 32) = x21 := by rw [rk38 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g37_21]
  have g38_25 : reg n38 (25 : Fin 32) = x25 := by rw [rk38 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [rk38 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk38 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g37_27]
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4)] := keep_kk37.trans K38
  clear keep_kk37
  have w38_24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := (K38.w32 (by decide) (by decide)).trans w37_24
  have w38_28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := (K38.w32 (by decide) (by decide)).trans w37_28
  have w38_2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := (K38.w32 (by decide) (by decide)).trans w37_2c
  have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := (K38.w32 (by decide) (by decide)).trans w37_30
  have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := (K38.w32 (by decide) (by decide)).trans w37_34
  have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := (K38.w32 (by decide) (by decide)).trans w37_38
  have w38_3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := (K38.w32 (by decide) (by decide)).trans w37_3c
  have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := (K38.w32 (by decide) (by decide)).trans w37_40
  have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := (K38.w32 (by decide) (by decide)).trans w37_44
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K38.w32 (by decide) (by decide)).trans w37_48
  have w38_4c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K38.w32 (by decide) (by decide)).trans w37_4c
  have w38_50 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K38.w32 (by decide) (by decide)).trans w37_50
  have w38_54 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K38.w32 (by decide) (by decide)).trans w37_54
  have w38_58 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K38.w32 (by decide) (by decide)).trans w37_58
  have w38_5c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K38.w32 (by decide) (by decide)).trans w37_5c
  have w38_60 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K38.w32 (by decide) (by decide)).trans w37_60
  have w38_64 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K38.w32 (by decide) (by decide)).trans w37_64
  have w38_68 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K38.w32 (by decide) (by decide)).trans w37_68
  have w38_6c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K38.w32 (by decide) (by decide)).trans w37_6c
  have w38_70 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K38.w32 (by decide) (by decide)).trans w37_70
  have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K38.w32 (by decide) (by decide)).trans w37_74
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K38.w32 (by decide) (by decide)).trans w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K38.w32 (by decide) (by decide)).trans w37_7c
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K38.w32 (by decide) (by decide)).trans w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K38.w32 (by decide) (by decide)).trans w37_84
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K38.w32 (by decide) (by decide)).trans w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K38.w32 (by decide) (by decide)).trans w37_8c
  have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K38.w32 (by decide) (by decide)).trans w37_90
  have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K38.w32 (by decide) (by decide)).trans w37_94
  have w38_a20 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K38.w32 (by decide) (by decide)).trans w37_a20
  have w38_a24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K38.w32 (by decide) (by decide)).trans w37_a24
  have w38_a28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K38.w32 (by decide) (by decide)).trans w37_a28
  have w38_a2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K38.w32 (by decide) (by decide)).trans w37_a2c
  have w38_a30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K38.w32 (by decide) (by decide)).trans w37_a30
  have w38_a34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K38.w32 (by decide) (by decide)).trans w37_a34
  have w38_a38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K38.w32 (by decide) (by decide)).trans w37_a38
  have w38_a3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K38.w32 (by decide) (by decide)).trans w37_a3c
  have w38_a40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K38.w32 (by decide) (by decide)).trans w37_a40
  have w38_a44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K38.w32 (by decide) (by decide)).trans w37_a44
  clear w37_a44 w37_a40 w37_a3c w37_a38 w37_a34 w37_a30 w37_a2c w37_a28 w37_a24 w37_a20 w37_94 w37_90 w37_8c w37_88 w37_84 w37_80 w37_7c w37_78 w37_74 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 w37_50 w37_4c w37_48 w37_44 w37_40 w37_3c w37_38 w37_34 w37_30 w37_2c w37_28 w37_24 g37_13 g37_27 g37_26 g37_25 g37_21 g37_19 g37_18 g37_12 g37_11 g37_10 g37_9 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
  by_cases hz_38 : memBytes M0 orp orl = memBytes M0 arp arl
  rotate_left
  · have g38_10 : reg n38 a0 = BitVec.ofNat 32 1 := by rw [a0_38, ite_eq_right hz_38]; rfl
    -- 0xA24: branch, taken
    obtain ⟨n39, d39, u39⟩ := s38.taken E38.self 0x966 sv_at_a24
      (by decide) (by rw [g38_10, s38.zero]; decide)
    have s39 : St n39.mem SV n39 0x966 (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
    have m39 : n39.mem = n38.mem := u39.mem
    have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
    have t39 : Steps n0 n39 := t38.trans (.single d39)
    have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
    have E39 : SvCode n39.mem := E38.fr F fr39
    have V39 : SvSaves B n39.mem v := V38.same m39
    have g39_2 : reg n39 sp = B + 0x21A0 := by rw [u39.regs, g38_2]
    have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u39.regs, g38_3]
    have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u39.regs, g38_4]
    have g39_9 : reg n39 (9 : Fin 32) = x9 := by rw [u39.regs, g38_9]
    have g39_10 : reg n39 a0 = BitVec.ofNat 32 0x1 := by rw [u39.regs, g38_10]
    have g39_18 : reg n39 (18 : Fin 32) = out := by rw [u39.regs, g38_18]
    have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [u39.regs, g38_19]
    have g39_21 : reg n39 (21 : Fin 32) = x21 := by rw [u39.regs, g38_21]
    have g39_25 : reg n39 (25 : Fin 32) = x25 := by rw [u39.regs, g38_25]
    have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [u39.regs, g38_26]
    have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u39.regs, g38_27]
    have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4)] := by rw [m39]; exact keep_kk38
    clear keep_kk38
    have w39_24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m39]; exact w38_24
    have w39_28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m39]; exact w38_28
    have w39_2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m39]; exact w38_2c
    have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m39]; exact w38_30
    have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m39]; exact w38_34
    have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m39]; exact w38_38
    have w39_3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m39]; exact w38_3c
    have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m39]; exact w38_40
    have w39_44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m39]; exact w38_44
    have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m39]; exact w38_48
    have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m39]; exact w38_4c
    have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m39]; exact w38_50
    have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m39]; exact w38_54
    have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m39]; exact w38_58
    have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m39]; exact w38_5c
    have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m39]; exact w38_60
    have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m39]; exact w38_64
    have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m39]; exact w38_68
    have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m39]; exact w38_6c
    have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m39]; exact w38_70
    have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m39]; exact w38_74
    have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m39]; exact w38_78
    have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m39]; exact w38_7c
    have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m39]; exact w38_80
    have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m39]; exact w38_84
    have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m39]; exact w38_88
    have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m39]; exact w38_8c
    have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m39]; exact w38_90
    have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m39]; exact w38_94
    have w39_a20 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m39]; exact w38_a20
    have w39_a24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m39]; exact w38_a24
    have w39_a28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m39]; exact w38_a28
    have w39_a2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m39]; exact w38_a2c
    have w39_a30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m39]; exact w38_a30
    have w39_a34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m39]; exact w38_a34
    have w39_a38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m39]; exact w38_a38
    have w39_a3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m39]; exact w38_a3c
    have w39_a40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m39]; exact w38_a40
    have w39_a44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m39]; exact w38_a44
    clear w38_a44 w38_a40 w38_a3c w38_a38 w38_a34 w38_a30 w38_a2c w38_a28 w38_a24 w38_a20 w38_94 w38_90 w38_8c w38_88 w38_84 w38_80 w38_7c w38_78 w38_74 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 w38_50 w38_4c w38_48 w38_44 w38_40 w38_3c w38_38 w38_34 w38_30 w38_2c w38_28 w38_24 g38_27 g38_26 g38_25 g38_21 g38_19 g38_18 g38_9 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 K38 a0_38 rk38 s38 c38
    exact .inl ⟨(fun ⟨h0', h1', h2', h3', h4', h5', _⟩ => by exact hz_38 h5'), sv_fail F E39 s39 t39 (fun x hx => (fR39 x hx).trans (fM x hx).symm) V39 hret g39_2 g39_18 hO g39_3 g39_4⟩
  have g38_10 : reg n38 a0 = BitVec.ofNat 32 0 := by rw [a0_38, ite_eq_left hz_38]; rfl
  -- 0xA24: branch, not taken
  obtain ⟨n39, d39, u39⟩ := s38.notTaken E38.self 0xA26 sv_at_a24
    (by decide) (by rw [g38_10, s38.zero]; decide)
  have s39 : St n39.mem SV n39 0xA26 (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
  have t39 : Steps n0 n39 := t38.trans (.single d39)
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.same m39
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [u39.regs, g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u39.regs, g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u39.regs, g38_4]
  have g39_9 : reg n39 (9 : Fin 32) = x9 := by rw [u39.regs, g38_9]
  have g39_10 : reg n39 a0 = BitVec.ofNat 32 0x0 := by rw [u39.regs, g38_10]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [u39.regs, g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [u39.regs, g38_19]
  have g39_21 : reg n39 (21 : Fin 32) = x21 := by rw [u39.regs, g38_21]
  have g39_25 : reg n39 (25 : Fin 32) = x25 := by rw [u39.regs, g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [u39.regs, g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u39.regs, g38_27]
  have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4)] := by rw [m39]; exact keep_kk38
  clear keep_kk38
  have w39_24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m39]; exact w38_24
  have w39_28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m39]; exact w38_28
  have w39_2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m39]; exact w38_2c
  have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m39]; exact w38_30
  have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m39]; exact w38_34
  have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m39]; exact w38_38
  have w39_3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m39]; exact w38_3c
  have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m39]; exact w38_40
  have w39_44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m39]; exact w38_44
  have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m39]; exact w38_48
  have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m39]; exact w38_4c
  have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m39]; exact w38_50
  have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m39]; exact w38_54
  have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m39]; exact w38_58
  have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m39]; exact w38_5c
  have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m39]; exact w38_60
  have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m39]; exact w38_64
  have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m39]; exact w38_68
  have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m39]; exact w38_6c
  have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m39]; exact w38_70
  have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m39]; exact w38_74
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m39]; exact w38_78
  have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m39]; exact w38_7c
  have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m39]; exact w38_80
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m39]; exact w38_84
  have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m39]; exact w38_88
  have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m39]; exact w38_8c
  have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m39]; exact w38_90
  have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m39]; exact w38_94
  have w39_a20 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m39]; exact w38_a20
  have w39_a24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m39]; exact w38_a24
  have w39_a28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m39]; exact w38_a28
  have w39_a2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m39]; exact w38_a2c
  have w39_a30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m39]; exact w38_a30
  have w39_a34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m39]; exact w38_a34
  have w39_a38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m39]; exact w38_a38
  have w39_a3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m39]; exact w38_a3c
  have w39_a40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m39]; exact w38_a40
  have w39_a44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m39]; exact w38_a44
  clear w38_a44 w38_a40 w38_a3c w38_a38 w38_a34 w38_a30 w38_a2c w38_a28 w38_a24 w38_a20 w38_94 w38_90 w38_8c w38_88 w38_84 w38_80 w38_7c w38_78 w38_74 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 w38_50 w38_4c w38_48 w38_44 w38_40 w38_3c w38_38 w38_34 w38_30 w38_2c w38_28 w38_24 g38_27 g38_26 g38_25 g38_21 g38_19 g38_18 g38_9 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 K38 a0_38 rk38 s38 c38
  -- 0xA26
  obtain ⟨n40, c40, u40⟩ := s39.block svL7a26 E39.self svL7a26_end
    ⟨trivial, trivial, trivial⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have s40 : St n40.mem SV n40 0xA2E (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have rb40 : ∀ q, reg n40 q = (runBlock svL7a26 (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
  have fr40 : ∀ x, SvR B x → n40.mem x = n39.mem x := fun x _ => by rw [m40]
  have t40 : Steps n0 n40 := t39.trans c40
  have fR40 : ∀ x, SvR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : SvCode n40.mem := E39.fr F fr40
  have V40 : SvSaves B n40.mem v := V39.same m40
  have g40_2 : reg n40 sp = B + 0x21A0 := by
    rw [rb40, runBlock_reg _ _ _ sp s39.zero (by decide), g39_2]
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb40, runBlock_reg _ _ _ (3 : Fin 32) s39.zero (by decide), g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb40, runBlock_reg _ _ _ (4 : Fin 32) s39.zero (by decide), g39_4]
  have g40_9 : reg n40 (9 : Fin 32) = x9 := by
    rw [rb40, runBlock_reg _ _ _ (9 : Fin 32) s39.zero (by decide), g39_9]
  have g40_18 : reg n40 (18 : Fin 32) = out := by
    rw [rb40, runBlock_reg _ _ _ (18 : Fin 32) s39.zero (by decide), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by
    rw [rb40, runBlock_reg _ _ _ (19 : Fin 32) s39.zero (by decide), g39_19]
  have g40_21 : reg n40 (21 : Fin 32) = x21 := by
    rw [rb40, runBlock_reg _ _ _ (21 : Fin 32) s39.zero (by decide), g39_21]
  have g40_25 : reg n40 (25 : Fin 32) = x25 := by
    rw [rb40, runBlock_reg _ _ _ (25 : Fin 32) s39.zero (by decide), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = x26 := by
    rw [rb40, runBlock_reg _ _ _ (26 : Fin 32) s39.zero (by decide), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb40, runBlock_reg _ _ _ (27 : Fin 32) s39.zero (by decide), g39_27]
  have g40_10 : reg n40 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svL7a26, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_9, g39_10, g39_18, g39_19, g39_21, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4)] := by rw [m40]; exact keep_kk39
  clear keep_kk39
  have w40_24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m40]; exact w39_24
  have w40_28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m40]; exact w39_28
  have w40_2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m40]; exact w39_2c
  have w40_30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m40]; exact w39_30
  have w40_34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m40]; exact w39_34
  have w40_38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m40]; exact w39_38
  have w40_3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m40]; exact w39_3c
  have w40_40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m40]; exact w39_40
  have w40_44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m40]; exact w39_44
  have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m40]; exact w39_48
  have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m40]; exact w39_4c
  have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m40]; exact w39_50
  have w40_54 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m40]; exact w39_54
  have w40_58 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m40]; exact w39_58
  have w40_5c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m40]; exact w39_5c
  have w40_60 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m40]; exact w39_60
  have w40_64 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m40]; exact w39_64
  have w40_68 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m40]; exact w39_68
  have w40_6c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m40]; exact w39_6c
  have w40_70 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m40]; exact w39_70
  have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m40]; exact w39_74
  have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m40]; exact w39_78
  have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m40]; exact w39_7c
  have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m40]; exact w39_80
  have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m40]; exact w39_84
  have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m40]; exact w39_88
  have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m40]; exact w39_8c
  have w40_90 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m40]; exact w39_90
  have w40_94 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m40]; exact w39_94
  have w40_a20 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m40]; exact w39_a20
  have w40_a24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m40]; exact w39_a24
  have w40_a28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m40]; exact w39_a28
  have w40_a2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m40]; exact w39_a2c
  have w40_a30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m40]; exact w39_a30
  have w40_a34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m40]; exact w39_a34
  have w40_a38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m40]; exact w39_a38
  have w40_a3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m40]; exact w39_a3c
  have w40_a40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m40]; exact w39_a40
  have w40_a44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m40]; exact w39_a44
  clear w39_a44 w39_a40 w39_a3c w39_a38 w39_a34 w39_a30 w39_a2c w39_a28 w39_a24 w39_a20 w39_94 w39_90 w39_8c w39_88 w39_84 w39_80 w39_7c w39_78 w39_74 w39_70 w39_6c w39_68 w39_64 w39_60 w39_5c w39_58 w39_54 w39_50 w39_4c w39_48 w39_44 w39_40 w39_3c w39_38 w39_34 w39_30 w39_2c w39_28 w39_24 g39_27 g39_26 g39_25 g39_21 g39_19 g39_18 g39_10 g39_9 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 m39 s39 u39 d39 g38_10
  -- 0xA2E: lw
  obtain ⟨n41, d41, u41⟩ := s40.lw E40.self sv_at_a2e (off' := 0xA30) (by decide)
    (by rw [g40_2, show B + 0x21A0 + 0x7C = B + 0x21A0 + BitVec.ofNat 32 0x7C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s41 : St n41.mem SV n41 0xA30 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
  have m41 : n41.mem = n40.mem := u41.mem
  have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
  have t41 : Steps n0 n41 := t40.trans (.single d41)
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.same m41
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, upd_ne (by decide) (by decide), g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, upd_ne (by decide) (by decide), g40_4]
  have g41_9 : reg n41 (9 : Fin 32) = x9 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_9]
  have g41_10 : reg n41 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_10]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [u41.regs, upd_ne (by decide) (by decide), g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [u41.regs, upd_ne (by decide) (by decide), g40_19]
  have g41_21 : reg n41 (21 : Fin 32) = x21 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_21]
  have g41_25 : reg n41 (25 : Fin 32) = x25 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = x26 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_27]
  have g41_11 : reg n41 a1 = sgp := by
    rw [u41.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g40_2, show B + 0x21A0 + 0x7C = B + 0x21A0 + BitVec.ofNat 32 0x7C by sv_addr, w40_7c]
  have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4)] := by rw [m41]; exact keep_kk40
  clear keep_kk40
  have w41_24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m41]; exact w40_24
  have w41_28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m41]; exact w40_28
  have w41_2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m41]; exact w40_2c
  have w41_30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m41]; exact w40_30
  have w41_34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m41]; exact w40_34
  have w41_38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m41]; exact w40_38
  have w41_3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m41]; exact w40_3c
  have w41_40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m41]; exact w40_40
  have w41_44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m41]; exact w40_44
  have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m41]; exact w40_48
  have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m41]; exact w40_4c
  have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m41]; exact w40_50
  have w41_54 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m41]; exact w40_54
  have w41_58 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m41]; exact w40_58
  have w41_5c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m41]; exact w40_5c
  have w41_60 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m41]; exact w40_60
  have w41_64 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m41]; exact w40_64
  have w41_68 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m41]; exact w40_68
  have w41_6c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m41]; exact w40_6c
  have w41_70 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m41]; exact w40_70
  have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m41]; exact w40_74
  have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m41]; exact w40_78
  have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m41]; exact w40_7c
  have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m41]; exact w40_80
  have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m41]; exact w40_84
  have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m41]; exact w40_88
  have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m41]; exact w40_8c
  have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m41]; exact w40_90
  have w41_94 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m41]; exact w40_94
  have w41_a20 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m41]; exact w40_a20
  have w41_a24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m41]; exact w40_a24
  have w41_a28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m41]; exact w40_a28
  have w41_a2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m41]; exact w40_a2c
  have w41_a30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m41]; exact w40_a30
  have w41_a34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m41]; exact w40_a34
  have w41_a38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m41]; exact w40_a38
  have w41_a3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m41]; exact w40_a3c
  have w41_a40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m41]; exact w40_a40
  have w41_a44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m41]; exact w40_a44
  clear w40_a44 w40_a40 w40_a3c w40_a38 w40_a34 w40_a30 w40_a2c w40_a28 w40_a24 w40_a20 w40_94 w40_90 w40_8c w40_88 w40_84 w40_80 w40_7c w40_78 w40_74 w40_70 w40_6c w40_68 w40_64 w40_60 w40_5c w40_58 w40_54 w40_50 w40_4c w40_48 w40_44 w40_40 w40_3c w40_38 w40_34 w40_30 w40_2c w40_28 w40_24 g40_10 g40_27 g40_26 g40_25 g40_21 g40_19 g40_18 g40_9 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
  -- 0xA30: lw
  obtain ⟨n42, d42, u42⟩ := s41.lw E41.self sv_at_a30 (off' := 0xA32) (by decide)
    (by rw [g41_2, show B + 0x21A0 + 0x68 = B + 0x21A0 + BitVec.ofNat 32 0x68 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s42 : St n42.mem SV n42 0xA32 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
  have t42 : Steps n0 n42 := t41.trans (.single d42)
  have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
  have E42 : SvCode n42.mem := E41.fr F fr42
  have V42 : SvSaves B n42.mem v := V41.same m42
  have g42_2 : reg n42 sp = B + 0x21A0 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_2]
  have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u42.regs, upd_ne (by decide) (by decide), g41_3]
  have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u42.regs, upd_ne (by decide) (by decide), g41_4]
  have g42_9 : reg n42 (9 : Fin 32) = x9 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_9]
  have g42_10 : reg n42 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_10]
  have g42_11 : reg n42 a1 = sgp := by rw [u42.regs, upd_ne (by decide) (by decide), g41_11]
  have g42_18 : reg n42 (18 : Fin 32) = out := by rw [u42.regs, upd_ne (by decide) (by decide), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by rw [u42.regs, upd_ne (by decide) (by decide), g41_19]
  have g42_21 : reg n42 (21 : Fin 32) = x21 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_21]
  have g42_25 : reg n42 (25 : Fin 32) = x25 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_25]
  have g42_26 : reg n42 (26 : Fin 32) = x26 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_26]
  have g42_27 : reg n42 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_27]
  have g42_12 : reg n42 a2 = BitVec.ofNat 32 sgl := by
    rw [u42.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g41_2, show B + 0x21A0 + 0x68 = B + 0x21A0 + BitVec.ofNat 32 0x68 by sv_addr, w41_68]
  have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4)] := by rw [m42]; exact keep_kk41
  clear keep_kk41
  have w42_24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m42]; exact w41_24
  have w42_28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m42]; exact w41_28
  have w42_2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m42]; exact w41_2c
  have w42_30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m42]; exact w41_30
  have w42_34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m42]; exact w41_34
  have w42_38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m42]; exact w41_38
  have w42_3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m42]; exact w41_3c
  have w42_40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m42]; exact w41_40
  have w42_44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m42]; exact w41_44
  have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m42]; exact w41_48
  have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m42]; exact w41_4c
  have w42_50 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m42]; exact w41_50
  have w42_54 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m42]; exact w41_54
  have w42_58 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m42]; exact w41_58
  have w42_5c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m42]; exact w41_5c
  have w42_60 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m42]; exact w41_60
  have w42_64 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m42]; exact w41_64
  have w42_68 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m42]; exact w41_68
  have w42_6c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m42]; exact w41_6c
  have w42_70 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m42]; exact w41_70
  have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m42]; exact w41_74
  have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m42]; exact w41_78
  have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m42]; exact w41_7c
  have w42_80 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m42]; exact w41_80
  have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m42]; exact w41_84
  have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m42]; exact w41_88
  have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m42]; exact w41_8c
  have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m42]; exact w41_90
  have w42_94 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m42]; exact w41_94
  have w42_a20 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m42]; exact w41_a20
  have w42_a24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m42]; exact w41_a24
  have w42_a28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m42]; exact w41_a28
  have w42_a2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m42]; exact w41_a2c
  have w42_a30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m42]; exact w41_a30
  have w42_a34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m42]; exact w41_a34
  have w42_a38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m42]; exact w41_a38
  have w42_a3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m42]; exact w41_a3c
  have w42_a40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m42]; exact w41_a40
  have w42_a44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m42]; exact w41_a44
  clear w41_a44 w41_a40 w41_a3c w41_a38 w41_a34 w41_a30 w41_a2c w41_a28 w41_a24 w41_a20 w41_94 w41_90 w41_8c w41_88 w41_84 w41_80 w41_7c w41_78 w41_74 w41_70 w41_6c w41_68 w41_64 w41_60 w41_5c w41_58 w41_54 w41_50 w41_4c w41_48 w41_44 w41_40 w41_3c w41_38 w41_34 w41_30 w41_2c w41_28 w41_24 g41_11 g41_27 g41_26 g41_25 g41_21 g41_19 g41_18 g41_10 g41_9 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
  -- 0xA32: sv_esF
  obtain ⟨n43, c43, s43, sp43, rk43, K43, R43, fr43⟩ := sv_esF (oc := 0xA20) (nl := sgl)
    F E42 s42 sv_at_a32 sv_at_a36 (by decide) (by decide) g42_2
    g42_10 g42_11 g42_12 (by decide) sg_in
  have t43 : Steps n0 n43 := t42.trans c43
  have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.keepL K43 (by decide)
  rw [ecdsaSigOf_congr (sv_pt fR42 sg_in)] at R43
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk43 (3 : Fin 32) (by decide), g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk43 (4 : Fin 32) (by decide), g42_4]
  have g43_9 : reg n43 (9 : Fin 32) = x9 := by rw [rk43 (9 : Fin 32) (by decide), g42_9]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [rk43 (18 : Fin 32) (by decide), g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [rk43 (19 : Fin 32) (by decide), g42_19]
  have g43_21 : reg n43 (21 : Fin 32) = x21 := by rw [rk43 (21 : Fin 32) (by decide), g42_21]
  have g43_25 : reg n43 (25 : Fin 32) = x25 := by rw [rk43 (25 : Fin 32) (by decide), g42_25]
  have g43_26 : reg n43 (26 : Fin 32) = x26 := by rw [rk43 (26 : Fin 32) (by decide), g42_26]
  have g43_27 : reg n43 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk43 (27 : Fin 32) (by decide), g42_27]
  have g43_2 : reg n43 sp = B + 0x21A0 := sp43
  obtain ⟨r43, hr43⟩ : ∃ r, ecdsaSigOf 48 M0 (sgp) (sgl) = r := ⟨_, rfl⟩
  rcases r43 with eb43 | ⟨sr43, ss43⟩
  · rw [hr43] at R43
    obtain ⟨y0_43, -⟩ := R43
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61)] := keep_kk42.trans K43
    clear keep_kk42
    have w43_24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := (K43.w32 (by decide) (by decide)).trans w42_24
    have w43_28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := (K43.w32 (by decide) (by decide)).trans w42_28
    have w43_2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := (K43.w32 (by decide) (by decide)).trans w42_2c
    have w43_30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := (K43.w32 (by decide) (by decide)).trans w42_30
    have w43_34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := (K43.w32 (by decide) (by decide)).trans w42_34
    have w43_38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := (K43.w32 (by decide) (by decide)).trans w42_38
    have w43_3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := (K43.w32 (by decide) (by decide)).trans w42_3c
    have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := (K43.w32 (by decide) (by decide)).trans w42_40
    have w43_44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := (K43.w32 (by decide) (by decide)).trans w42_44
    have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K43.w32 (by decide) (by decide)).trans w42_48
    have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K43.w32 (by decide) (by decide)).trans w42_4c
    have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K43.w32 (by decide) (by decide)).trans w42_50
    have w43_54 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K43.w32 (by decide) (by decide)).trans w42_54
    have w43_58 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K43.w32 (by decide) (by decide)).trans w42_58
    have w43_5c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K43.w32 (by decide) (by decide)).trans w42_5c
    have w43_60 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K43.w32 (by decide) (by decide)).trans w42_60
    have w43_64 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K43.w32 (by decide) (by decide)).trans w42_64
    have w43_68 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K43.w32 (by decide) (by decide)).trans w42_68
    have w43_6c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K43.w32 (by decide) (by decide)).trans w42_6c
    have w43_70 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K43.w32 (by decide) (by decide)).trans w42_70
    have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K43.w32 (by decide) (by decide)).trans w42_74
    have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K43.w32 (by decide) (by decide)).trans w42_78
    have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K43.w32 (by decide) (by decide)).trans w42_7c
    have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K43.w32 (by decide) (by decide)).trans w42_80
    have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K43.w32 (by decide) (by decide)).trans w42_84
    have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K43.w32 (by decide) (by decide)).trans w42_88
    have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K43.w32 (by decide) (by decide)).trans w42_8c
    have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K43.w32 (by decide) (by decide)).trans w42_90
    have w43_94 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K43.w32 (by decide) (by decide)).trans w42_94
    have b43_a20 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := y0_43
    clear w42_a44 w42_a40 w42_a3c w42_a38 w42_a34 w42_a30 w42_a2c w42_a28 w42_a24 w42_a20 w42_94 w42_90 w42_8c w42_88 w42_84 w42_80 w42_7c w42_78 w42_74 w42_70 w42_6c w42_68 w42_64 w42_60 w42_5c w42_58 w42_54 w42_50 w42_4c w42_48 w42_44 w42_40 w42_3c w42_38 w42_34 w42_30 w42_2c w42_28 w42_24 g42_12 g42_27 g42_26 g42_25 g42_21 g42_19 g42_18 g42_11 g42_10 g42_9 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 m42 s42 u42 d42
    -- 0xA3A: lbu
    obtain ⟨n44, d44, u44⟩ := s43.lbu E43.self sv_at_a3a (off' := 0xA3E) (by decide)
    have s44 : St n44.mem SV n44 0xA3E (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
    have m44 : n44.mem = n43.mem := u44.mem
    have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
    have t44 : Steps n0 n44 := t43.trans (.single d44)
    have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
    have E44 : SvCode n44.mem := E43.fr F fr44
    have V44 : SvSaves B n44.mem v := V43.same m44
    have g44_2 : reg n44 sp = B + 0x21A0 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_2]
    have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_3]
    have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_4]
    have g44_9 : reg n44 (9 : Fin 32) = x9 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_9]
    have g44_18 : reg n44 (18 : Fin 32) = out := by rw [u44.regs, upd_ne (by decide) (by decide), g43_18]
    have g44_19 : reg n44 (19 : Fin 32) = bp := by rw [u44.regs, upd_ne (by decide) (by decide), g43_19]
    have g44_21 : reg n44 (21 : Fin 32) = x21 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_21]
    have g44_25 : reg n44 (25 : Fin 32) = x25 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_25]
    have g44_26 : reg n44 (26 : Fin 32) = x26 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_26]
    have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_27]
    have g44_10 : reg n44 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u44.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g43_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b43_a20]
    have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61)] := by rw [m44]; exact keep_kk43
    clear keep_kk43
    have w44_24 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m44]; exact w43_24
    have w44_28 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m44]; exact w43_28
    have w44_2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m44]; exact w43_2c
    have w44_30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m44]; exact w43_30
    have w44_34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m44]; exact w43_34
    have w44_38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m44]; exact w43_38
    have w44_3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m44]; exact w43_3c
    have w44_40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m44]; exact w43_40
    have w44_44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m44]; exact w43_44
    have w44_48 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m44]; exact w43_48
    have w44_4c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m44]; exact w43_4c
    have w44_50 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m44]; exact w43_50
    have w44_54 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m44]; exact w43_54
    have w44_58 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m44]; exact w43_58
    have w44_5c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m44]; exact w43_5c
    have w44_60 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m44]; exact w43_60
    have w44_64 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m44]; exact w43_64
    have w44_68 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m44]; exact w43_68
    have w44_6c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m44]; exact w43_6c
    have w44_70 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m44]; exact w43_70
    have w44_74 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m44]; exact w43_74
    have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m44]; exact w43_78
    have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m44]; exact w43_7c
    have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m44]; exact w43_80
    have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m44]; exact w43_84
    have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m44]; exact w43_88
    have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m44]; exact w43_8c
    have w44_90 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m44]; exact w43_90
    have w44_94 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m44]; exact w43_94
    have b44_a20 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m44]; exact b43_a20
    clear b43_a20 w43_94 w43_90 w43_8c w43_88 w43_84 w43_80 w43_7c w43_78 w43_74 w43_70 w43_6c w43_68 w43_64 w43_60 w43_5c w43_58 w43_54 w43_50 w43_4c w43_48 w43_44 w43_40 w43_3c w43_38 w43_34 w43_30 w43_2c w43_28 w43_24 y0_43
    -- 0xA3E: lbu
    obtain ⟨n45, d45, u45⟩ := s44.lbu E44.self sv_at_a3e (off' := 0xA42) (by decide)
    have s45 : St n45.mem SV n45 0xA42 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
    have m45 : n45.mem = n44.mem := u45.mem
    have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
    have t45 : Steps n0 n45 := t44.trans (.single d45)
    have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
    have E45 : SvCode n45.mem := E44.fr F fr45
    have V45 : SvSaves B n45.mem v := V44.same m45
    have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_2]
    have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, upd_ne (by decide) (by decide), g44_3]
    have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, upd_ne (by decide) (by decide), g44_4]
    have g45_9 : reg n45 (9 : Fin 32) = x9 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_9]
    have g45_10 : reg n45 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_10]
    have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, upd_ne (by decide) (by decide), g44_18]
    have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, upd_ne (by decide) (by decide), g44_19]
    have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_21]
    have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_25]
    have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_26]
    have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_27]
    have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61)] := by rw [m45]; exact keep_kk44
    clear keep_kk44
    have w45_24 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m45]; exact w44_24
    have w45_28 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m45]; exact w44_28
    have w45_2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m45]; exact w44_2c
    have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m45]; exact w44_30
    have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m45]; exact w44_34
    have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m45]; exact w44_38
    have w45_3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m45]; exact w44_3c
    have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m45]; exact w44_40
    have w45_44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m45]; exact w44_44
    have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m45]; exact w44_48
    have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m45]; exact w44_4c
    have w45_50 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m45]; exact w44_50
    have w45_54 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m45]; exact w44_54
    have w45_58 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m45]; exact w44_58
    have w45_5c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m45]; exact w44_5c
    have w45_60 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m45]; exact w44_60
    have w45_64 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m45]; exact w44_64
    have w45_68 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m45]; exact w44_68
    have w45_6c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m45]; exact w44_6c
    have w45_70 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m45]; exact w44_70
    have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m45]; exact w44_74
    have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m45]; exact w44_78
    have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m45]; exact w44_7c
    have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m45]; exact w44_80
    have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m45]; exact w44_84
    have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m45]; exact w44_88
    have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m45]; exact w44_8c
    have w45_90 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m45]; exact w44_90
    have w45_94 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m45]; exact w44_94
    have b45_a20 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m45]; exact b44_a20
    clear b44_a20 w44_94 w44_90 w44_8c w44_88 w44_84 w44_80 w44_7c w44_78 w44_74 w44_70 w44_6c w44_68 w44_64 w44_60 w44_5c w44_58 w44_54 w44_50 w44_4c w44_48 w44_44 w44_40 w44_3c w44_38 w44_34 w44_30 w44_2c w44_28 w44_24 g44_10 g44_27 g44_26 g44_25 g44_21 g44_19 g44_18 g44_9 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 m44 s44 u44 d44
    -- 0xA42: branch, taken
    obtain ⟨n46, d46, u46⟩ := s45.taken E45.self 0x966 sv_at_a42
      (by decide) (by rw [g45_10, s45.zero]; decide)
    have s46 : St n46.mem SV n46 0x966 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
    have m46 : n46.mem = n45.mem := u46.mem
    have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
    have t46 : Steps n0 n46 := t45.trans (.single d46)
    have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
    have E46 : SvCode n46.mem := E45.fr F fr46
    have V46 : SvSaves B n46.mem v := V45.same m46
    have g46_2 : reg n46 sp = B + 0x21A0 := by rw [u46.regs, g45_2]
    have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u46.regs, g45_3]
    have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u46.regs, g45_4]
    have g46_9 : reg n46 (9 : Fin 32) = x9 := by rw [u46.regs, g45_9]
    have g46_10 : reg n46 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u46.regs, g45_10]
    have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, g45_18]
    have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, g45_19]
    have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, g45_21]
    have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, g45_25]
    have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, g45_26]
    have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u46.regs, g45_27]
    have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61)] := by rw [m46]; exact keep_kk45
    clear keep_kk45
    have w46_24 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m46]; exact w45_24
    have w46_28 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m46]; exact w45_28
    have w46_2c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m46]; exact w45_2c
    have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m46]; exact w45_30
    have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m46]; exact w45_34
    have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m46]; exact w45_38
    have w46_3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m46]; exact w45_3c
    have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m46]; exact w45_40
    have w46_44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m46]; exact w45_44
    have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m46]; exact w45_48
    have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m46]; exact w45_4c
    have w46_50 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m46]; exact w45_50
    have w46_54 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m46]; exact w45_54
    have w46_58 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m46]; exact w45_58
    have w46_5c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m46]; exact w45_5c
    have w46_60 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m46]; exact w45_60
    have w46_64 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m46]; exact w45_64
    have w46_68 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m46]; exact w45_68
    have w46_6c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m46]; exact w45_6c
    have w46_70 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m46]; exact w45_70
    have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m46]; exact w45_74
    have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m46]; exact w45_78
    have w46_7c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m46]; exact w45_7c
    have w46_80 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m46]; exact w45_80
    have w46_84 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m46]; exact w45_84
    have w46_88 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m46]; exact w45_88
    have w46_8c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m46]; exact w45_8c
    have w46_90 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m46]; exact w45_90
    have w46_94 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m46]; exact w45_94
    have b46_a20 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m46]; exact b45_a20
    clear b45_a20 w45_94 w45_90 w45_8c w45_88 w45_84 w45_80 w45_7c w45_78 w45_74 w45_70 w45_6c w45_68 w45_64 w45_60 w45_5c w45_58 w45_54 w45_50 w45_4c w45_48 w45_44 w45_40 w45_3c w45_38 w45_34 w45_30 w45_2c w45_28 w45_24 g45_27 g45_26 g45_25 g45_21 g45_19 g45_18 g45_10 g45_9 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45
    exact .inl ⟨(fun ⟨h0', h1', h2', h3', h4', h5', sr43', ss43', h6', _⟩ => by rw [hr43] at h6'; cases h6'), sv_fail F E46 s46 t46 (fun x hx => (fR46 x hx).trans (fM x hx).symm) V46 hret g46_2 g46_18 hO g46_3 g46_4⟩
  rw [hr43] at R43
  obtain ⟨y0_43, yr_43, ys_43⟩ := R43
  have q43_a21 : ∀ j, j < 48 → n43.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => by rw [show 0xA21 + j = 0xA20 + 1 + j by omega]; exact yr_43 j hj
  have q43_a51 : ∀ j, j < 48 → n43.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [show 0xA51 + j = 0xA20 + 49 + j by omega]; exact ys_43 j hj
  have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61)] := keep_kk42.trans K43
  clear keep_kk42
  have w43_24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := (K43.w32 (by decide) (by decide)).trans w42_24
  have w43_28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := (K43.w32 (by decide) (by decide)).trans w42_28
  have w43_2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := (K43.w32 (by decide) (by decide)).trans w42_2c
  have w43_30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := (K43.w32 (by decide) (by decide)).trans w42_30
  have w43_34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := (K43.w32 (by decide) (by decide)).trans w42_34
  have w43_38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := (K43.w32 (by decide) (by decide)).trans w42_38
  have w43_3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := (K43.w32 (by decide) (by decide)).trans w42_3c
  have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := (K43.w32 (by decide) (by decide)).trans w42_40
  have w43_44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := (K43.w32 (by decide) (by decide)).trans w42_44
  have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := (K43.w32 (by decide) (by decide)).trans w42_48
  have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K43.w32 (by decide) (by decide)).trans w42_4c
  have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K43.w32 (by decide) (by decide)).trans w42_50
  have w43_54 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K43.w32 (by decide) (by decide)).trans w42_54
  have w43_58 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K43.w32 (by decide) (by decide)).trans w42_58
  have w43_5c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K43.w32 (by decide) (by decide)).trans w42_5c
  have w43_60 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K43.w32 (by decide) (by decide)).trans w42_60
  have w43_64 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := (K43.w32 (by decide) (by decide)).trans w42_64
  have w43_68 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := (K43.w32 (by decide) (by decide)).trans w42_68
  have w43_6c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K43.w32 (by decide) (by decide)).trans w42_6c
  have w43_70 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K43.w32 (by decide) (by decide)).trans w42_70
  have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := (K43.w32 (by decide) (by decide)).trans w42_74
  have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K43.w32 (by decide) (by decide)).trans w42_78
  have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K43.w32 (by decide) (by decide)).trans w42_7c
  have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K43.w32 (by decide) (by decide)).trans w42_80
  have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K43.w32 (by decide) (by decide)).trans w42_84
  have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K43.w32 (by decide) (by decide)).trans w42_88
  have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K43.w32 (by decide) (by decide)).trans w42_8c
  have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K43.w32 (by decide) (by decide)).trans w42_90
  have w43_94 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := (K43.w32 (by decide) (by decide)).trans w42_94
  have b43_a20 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := y0_43
  clear w42_a44 w42_a40 w42_a3c w42_a38 w42_a34 w42_a30 w42_a2c w42_a28 w42_a24 w42_a20 w42_94 w42_90 w42_8c w42_88 w42_84 w42_80 w42_7c w42_78 w42_74 w42_70 w42_6c w42_68 w42_64 w42_60 w42_5c w42_58 w42_54 w42_50 w42_4c w42_48 w42_44 w42_40 w42_3c w42_38 w42_34 w42_30 w42_2c w42_28 w42_24 g42_12 g42_27 g42_26 g42_25 g42_21 g42_19 g42_18 g42_11 g42_10 g42_9 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 m42 s42 u42 d42
  -- 0xA3A: lbu
  obtain ⟨n44, d44, u44⟩ := s43.lbu E43.self sv_at_a3a (off' := 0xA3E) (by decide)
  have s44 : St n44.mem SV n44 0xA3E (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
  have t44 : Steps n0 n44 := t43.trans (.single d44)
  have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
  have E44 : SvCode n44.mem := E43.fr F fr44
  have V44 : SvSaves B n44.mem v := V43.same m44
  have g44_2 : reg n44 sp = B + 0x21A0 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_2]
  have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_3]
  have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_4]
  have g44_9 : reg n44 (9 : Fin 32) = x9 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_9]
  have g44_18 : reg n44 (18 : Fin 32) = out := by rw [u44.regs, upd_ne (by decide) (by decide), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = bp := by rw [u44.regs, upd_ne (by decide) (by decide), g43_19]
  have g44_21 : reg n44 (21 : Fin 32) = x21 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_21]
  have g44_25 : reg n44 (25 : Fin 32) = x25 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_25]
  have g44_26 : reg n44 (26 : Fin 32) = x26 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_26]
  have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_27]
  have g44_10 : reg n44 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u44.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g43_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b43_a20]
  have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61)] := by rw [m44]; exact keep_kk43
  clear keep_kk43
  have w44_24 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m44]; exact w43_24
  have w44_28 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m44]; exact w43_28
  have w44_2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m44]; exact w43_2c
  have w44_30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m44]; exact w43_30
  have w44_34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m44]; exact w43_34
  have w44_38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m44]; exact w43_38
  have w44_3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m44]; exact w43_3c
  have w44_40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m44]; exact w43_40
  have w44_44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m44]; exact w43_44
  have w44_48 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m44]; exact w43_48
  have w44_4c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m44]; exact w43_4c
  have w44_50 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m44]; exact w43_50
  have w44_54 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m44]; exact w43_54
  have w44_58 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m44]; exact w43_58
  have w44_5c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m44]; exact w43_5c
  have w44_60 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m44]; exact w43_60
  have w44_64 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m44]; exact w43_64
  have w44_68 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m44]; exact w43_68
  have w44_6c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m44]; exact w43_6c
  have w44_70 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m44]; exact w43_70
  have w44_74 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m44]; exact w43_74
  have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m44]; exact w43_78
  have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m44]; exact w43_7c
  have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m44]; exact w43_80
  have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m44]; exact w43_84
  have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m44]; exact w43_88
  have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m44]; exact w43_8c
  have w44_90 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m44]; exact w43_90
  have w44_94 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m44]; exact w43_94
  have b44_a20 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m44]; exact b43_a20
  have q44_a21 : ∀ j, j < 48 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => by rw [m44]; exact q43_a21 j hj
  have q44_a51 : ∀ j, j < 48 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [m44]; exact q43_a51 j hj
  clear b43_a20 w43_94 w43_90 w43_8c w43_88 w43_84 w43_80 w43_7c w43_78 w43_74 w43_70 w43_6c w43_68 w43_64 w43_60 w43_5c w43_58 w43_54 w43_50 w43_4c w43_48 w43_44 w43_40 w43_3c w43_38 w43_34 w43_30 w43_2c w43_28 w43_24 q43_a51 q43_a21 ys_43 yr_43 y0_43 g43_2 g43_27 g43_26 g43_25 g43_21 g43_19 g43_18 g43_9 g43_4 g43_3 V43 E43 fR43 t43 fr43 K43 rk43 sp43 s43 c43
  -- 0xA3E: lbu
  have b44_a21 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA21) = BitVec.ofNat 8 ((sr43).getD 0 0) := q44_a21 0 (by decide)
  obtain ⟨n45, d45, u45⟩ := s44.lbu E44.self sv_at_a3e (off' := 0xA42) (by decide)
  have s45 : St n45.mem SV n45 0xA42 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
  have m45 : n45.mem = n44.mem := u45.mem
  have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
  have t45 : Steps n0 n45 := t44.trans (.single d45)
  have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.same m45
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, upd_ne (by decide) (by decide), g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, upd_ne (by decide) (by decide), g44_4]
  have g45_9 : reg n45 (9 : Fin 32) = x9 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_9]
  have g45_10 : reg n45 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_10]
  have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, upd_ne (by decide) (by decide), g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, upd_ne (by decide) (by decide), g44_19]
  have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_21]
  have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_25]
  have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_26]
  have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_27]
  have g45_20 : reg n45 (20 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 := by
    rw [u45.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g44_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x1 = B + 0x21A0 + BitVec.ofNat 32 0xA21 by sv_addr, b44_a21]
  have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61)] := by rw [m45]; exact keep_kk44
  clear keep_kk44
  have w45_24 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m45]; exact w44_24
  have w45_28 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m45]; exact w44_28
  have w45_2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m45]; exact w44_2c
  have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m45]; exact w44_30
  have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m45]; exact w44_34
  have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m45]; exact w44_38
  have w45_3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m45]; exact w44_3c
  have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m45]; exact w44_40
  have w45_44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m45]; exact w44_44
  have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m45]; exact w44_48
  have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m45]; exact w44_4c
  have w45_50 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m45]; exact w44_50
  have w45_54 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m45]; exact w44_54
  have w45_58 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m45]; exact w44_58
  have w45_5c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m45]; exact w44_5c
  have w45_60 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m45]; exact w44_60
  have w45_64 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m45]; exact w44_64
  have w45_68 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m45]; exact w44_68
  have w45_6c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m45]; exact w44_6c
  have w45_70 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m45]; exact w44_70
  have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m45]; exact w44_74
  have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m45]; exact w44_78
  have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m45]; exact w44_7c
  have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m45]; exact w44_80
  have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m45]; exact w44_84
  have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m45]; exact w44_88
  have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m45]; exact w44_8c
  have w45_90 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m45]; exact w44_90
  have w45_94 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m45]; exact w44_94
  have b45_a20 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m45]; exact b44_a20
  have b45_a21 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA21) = BitVec.ofNat 8 ((sr43).getD 0 0) := by rw [m45]; exact b44_a21
  have q45_a21 : ∀ j, j < 48 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => by rw [m45]; exact q44_a21 j hj
  have q45_a51 : ∀ j, j < 48 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [m45]; exact q44_a51 j hj
  clear q44_a51 q44_a21 b44_a20 w44_94 w44_90 w44_8c w44_88 w44_84 w44_80 w44_7c w44_78 w44_74 w44_70 w44_6c w44_68 w44_64 w44_60 w44_5c w44_58 w44_54 w44_50 w44_4c w44_48 w44_44 w44_40 w44_3c w44_38 w44_34 w44_30 w44_2c w44_28 w44_24 g44_10 g44_27 g44_26 g44_25 g44_21 g44_19 g44_18 g44_9 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 m44 s44 u44 d44
  -- 0xA42: branch, not taken
  obtain ⟨n46, d46, u46⟩ := s45.notTaken E45.self 0xA44 sv_at_a42
    (by decide) (by rw [g45_10, s45.zero]; decide)
  have s46 : St n46.mem SV n46 0xA44 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
  have m46 : n46.mem = n45.mem := u46.mem
  have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
  have t46 : Steps n0 n46 := t45.trans (.single d46)
  have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.same m46
  have g46_2 : reg n46 sp = B + 0x21A0 := by rw [u46.regs, g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u46.regs, g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u46.regs, g45_4]
  have g46_9 : reg n46 (9 : Fin 32) = x9 := by rw [u46.regs, g45_9]
  have g46_10 : reg n46 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u46.regs, g45_10]
  have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, g45_19]
  have g46_20 : reg n46 (20 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 := by rw [u46.regs, g45_20]
  have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, g45_21]
  have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, g45_25]
  have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, g45_26]
  have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u46.regs, g45_27]
  have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61)] := by rw [m46]; exact keep_kk45
  clear keep_kk45
  have w46_24 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9 := by rw [m46]; exact w45_24
  have w46_28 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7 := by rw [m46]; exact w45_28
  have w46_2c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5 := by rw [m46]; exact w45_2c
  have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3 := by rw [m46]; exact w45_30
  have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1 := by rw [m46]; exact w45_34
  have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8 := by rw [m46]; exact w45_38
  have w46_3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6 := by rw [m46]; exact w45_3c
  have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4 := by rw [m46]; exact w45_40
  have w46_44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2 := by rw [m46]; exact w45_44
  have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0 := by rw [m46]; exact w45_48
  have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m46]; exact w45_4c
  have w46_50 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m46]; exact w45_50
  have w46_54 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m46]; exact w45_54
  have w46_58 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m46]; exact w45_58
  have w46_5c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m46]; exact w45_5c
  have w46_60 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m46]; exact w45_60
  have w46_64 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 orl := by rw [m46]; exact w45_64
  have w46_68 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 sgl := by rw [m46]; exact w45_68
  have w46_6c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m46]; exact w45_6c
  have w46_70 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m46]; exact w45_70
  have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 arl := by rw [m46]; exact w45_74
  have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m46]; exact w45_78
  have w46_7c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m46]; exact w45_7c
  have w46_80 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m46]; exact w45_80
  have w46_84 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m46]; exact w45_84
  have w46_88 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m46]; exact w45_88
  have w46_8c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m46]; exact w45_8c
  have w46_90 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m46]; exact w45_90
  have w46_94 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem := by rw [m46]; exact w45_94
  have b46_a20 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m46]; exact b45_a20
  have b46_a21 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA21) = BitVec.ofNat 8 ((sr43).getD 0 0) := by rw [m46]; exact b45_a21
  have q46_a21 : ∀ j, j < 48 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => by rw [m46]; exact q45_a21 j hj
  have q46_a51 : ∀ j, j < 48 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [m46]; exact q45_a51 j hj
  clear q45_a51 q45_a21 b45_a21 b45_a20 w45_94 w45_90 w45_8c w45_88 w45_84 w45_80 w45_7c w45_78 w45_74 w45_70 w45_6c w45_68 w45_64 w45_60 w45_5c w45_58 w45_54 w45_50 w45_4c w45_48 w45_44 w45_40 w45_3c w45_38 w45_34 w45_30 w45_2c w45_28 w45_24 g45_20 g45_27 g45_26 g45_25 g45_21 g45_19 g45_18 g45_10 g45_9 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45 b44_a21
  exact .inr ⟨hz_4, hz_7, hz_10, hz_13, hz_21, hz_38, sr43, ss43, hr43, n46, t46, s46, E46, V46, fR46, g46_2, g46_3, g46_4, g46_9, g46_18, g46_19, g46_20, g46_21, g46_25, g46_26, g46_27, w46_24, w46_28, w46_2c, w46_30, w46_34, w46_38, w46_3c, w46_40, w46_44, w46_48, w46_4c, w46_50, w46_54, w46_58, w46_5c, w46_60, w46_64, w46_68, w46_6c, w46_70, w46_74, w46_78, w46_7c, w46_80, w46_84, w46_88, w46_8c, w46_90, w46_94, q46_a21, q46_a51, keep_kk46.mono (by decide)⟩

end C3.RV32.Sv
