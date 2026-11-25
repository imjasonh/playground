import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: the timestamp's signature algorithm

The signed attributes loop's exit at 0xFF8 to 0x10A4: both a message digest and a content type were seen, the `SignerInfo`'s signature algorithm is ecdsa-with-SHA384 with no parameters, its signature is a DER ECDSA signature with 48-byte scalars, and nothing follows it.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTrx1002 : List BInstr :=
  [.alu .sltu a0 x0 a0]
theorem svTrx1002_end : blockEnd sigstoreVerifyCode 0x1002 svTrx1002 = some 0x1006 := by
  simp only [svTrx1002]
  rw [blockEnd, sv_at_1002]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrx1008 : List BInstr :=
  [.alu .and a0 a0 a1]
theorem svTrx1008_end : blockEnd sigstoreVerifyCode 0x1008 svTrx1008 = some 0x100A := by
  simp only [svTrx1008]
  rw [blockEnd, sv_at_1008]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrx12b8 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x18]
theorem svTrx12b8_end : blockEnd sigstoreVerifyCode 0x12B8 svTrx12b8 = some 0x12BA := by
  simp only [svTrx12b8]
  rw [blockEnd, sv_at_12b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrx100e : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x370]
theorem svTrx100e_end : blockEnd sigstoreVerifyCode 0x100E svTrx100e = some 0x1014 := by
  simp only [svTrx100e]
  rw [blockEnd, sv_at_100e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1012]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrx102c : List BInstr :=
  [.lui a2 0x3FCC4000, .aluImm .add a2 a2 0x708, .aluImm .add a3 x0 0x8]
theorem svTrx102c_end : blockEnd sigstoreVerifyCode 0x102C svTrx102c = some 0x1036 := by
  simp only [svTrx102c]
  rw [blockEnd, sv_at_102c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1030]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1034]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrx103e : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x18]
theorem svTrx103e_end : blockEnd sigstoreVerifyCode 0x103E svTrx103e = some 0x1040 := by
  simp only [svTrx103e]
  rw [blockEnd, sv_at_103e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrx1048 : List BInstr :=
  [.aluImm .add a0 sp 0x400, .aluImm .add a1 sp 0x370]
theorem svTrx1048_end : blockEnd sigstoreVerifyCode 0x1048 svTrx1048 = some 0x104E := by
  simp only [svTrx1048]
  rw [blockEnd, sv_at_1048]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_104c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrx1060 : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svTrx1060_end : blockEnd sigstoreVerifyCode 0x1060 svTrx1060 = some 0x1064 := by
  simp only [svTrx1060]
  rw [blockEnd, sv_at_1060]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrx1076 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 (25 : Fin 32)]
theorem svTrx1076_end : blockEnd sigstoreVerifyCode 0x1076 svTrx1076 = some 0x1078 := by
  simp only [svTrx1076]
  rw [blockEnd, sv_at_1076]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrx108a : List BInstr :=
  [.aluImm .add a1 sp 0x422, .aluImm .add a0 sp 0x380, .aluImm .add a2 x0 0x5F]
theorem svTrx108a_end : blockEnd sigstoreVerifyCode 0x108A svTrx108a = some 0x1094 := by
  simp only [svTrx108a]
  rw [blockEnd, sv_at_108a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_108e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1090]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_trx {B out bp x20 x21 x22 x23 x24 x25 dg flag p0 L0 cp rem sip sil : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xFF8 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag)
    (w0_25c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0)
    (w0_260 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0)
    (w0_264 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp)
    (w0_268 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem)
    (w0_378 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip)
    (w0_37c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil)
    (cr_in : SvIn B (cp) (rem).toNat)
    (p0_in : SvIn B (p0) (L0).toNat)
    (si_in : SvIn B (sip) (sil).toNat)
    (hrem : rem = 0)
    (hflag : flag = 0 ∨ flag = 1) :
    (¬ ((dg ≠ 0 ∧ flag = 1) ∧ ∃ op9 ol9, derAlgOf M0 (sip) ((sil).toNat) = .ok ((op9, ol9), none) ∧ ∃ te9, derElement 0x30 (memBytes M0 (sip) (sil).toNat) = .ok te9 ∧ (memBytes M0 op9 ol9 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress)) 8) ∧ ∃ vp20 vl20, derContent ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) (derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) ((sil) - BitVec.ofNat 32 (te9.header + te9.len)).toNat)) = .ok (vp20, vl20) ∧ ∃ te20, derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) ((sil) - BitVec.ofNat 32 (te9.header + te9.len)).toNat) = .ok te20 ∧ ∃ sr25 ss25, ecdsaSigOf 48 M0 (vp20) ((vl20).toNat) = .ok (sr25, ss25) ∧ (((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((dg ≠ 0 ∧ flag = 1) ∧
    ∃ op9 ol9, derAlgOf M0 (sip) ((sil).toNat) = .ok ((op9, ol9), none) ∧
    ∃ te9, derElement 0x30 (memBytes M0 (sip) (sil).toNat) = .ok te9 ∧
    (memBytes M0 op9 ol9 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress)) 8) ∧
    ∃ vp20 vl20, derContent ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) (derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) ((sil) - BitVec.ofNat 32 (te9.header + te9.len)).toNat)) = .ok (vp20, vl20) ∧
    ∃ te20, derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) ((sil) - BitVec.ofNat 32 (te9.header + te9.len)).toNat) = .ok te20 ∧
    ∃ sr25 ss25, ecdsaSigOf 48 M0 (vp20) ((vl20).toNat) = .ok (sr25, ss25) ∧
    (((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x10A4 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = rem ∧
        reg n' (25 : Fin 32) = (BitVec.ofNat 8 ((sr25).getD 0 0)).zeroExtend 32 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 ((sr25).getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 ((ss25).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61), (0x380, 0x5F)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xFF8: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_ff8 (off' := 0xFFC) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x268 = B + 0x21A0 + BitVec.ofNat 32 0x268 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0xFFC (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, upd_ne (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_23]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = x27 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_24 : reg n1 (24 : Fin 32) = rem := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x268 = B + 0x21A0 + BitVec.ofNat 32 0x268 by sv_addr, w0_268]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m1]; exact w0_64
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m1]; exact w0_7c
  have w1_25c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m1]; exact w0_25c
  have w1_260 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m1]; exact w0_260
  have w1_264 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m1]; exact w0_264
  have w1_268 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m1]; exact w0_268
  have w1_378 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m1]; exact w0_378
  have w1_37c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m1]; exact w0_37c
  -- 0xFFC: branch, not taken
  obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.self 0x1000 sv_at_ffc
    (by decide) (by rw [g1_24, s1.zero]; exact br_bne_f hrem)
  have s2 : St n2.mem SV n2 0x1000 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, g1_4]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [u2.regs, g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [u2.regs, g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [u2.regs, g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = rem := by rw [u2.regs, g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [u2.regs, g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = x27 := by rw [u2.regs, g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m2]; exact w1_64
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m2]; exact w1_7c
  have w2_25c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m2]; exact w1_25c
  have w2_260 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m2]; exact w1_260
  have w2_264 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m2]; exact w1_264
  have w2_268 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m2]; exact w1_268
  have w2_378 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m2]; exact w1_378
  have w2_37c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m2]; exact w1_37c
  clear w1_37c w1_378 w1_268 w1_264 w1_260 w1_25c w1_7c w1_64 g1_24 g1_27 g1_26 g1_25 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x1000: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_1000 (off' := 0x1002) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x1002 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = rem := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_10 : reg n3 a0 = dg := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr, w2_64]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m3]; exact w2_64
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m3]; exact w2_7c
  have w3_25c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m3]; exact w2_25c
  have w3_260 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m3]; exact w2_260
  have w3_264 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m3]; exact w2_264
  have w3_268 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m3]; exact w2_268
  have w3_378 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m3]; exact w2_378
  have w3_37c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m3]; exact w2_37c
  clear w2_37c w2_378 w2_268 w2_264 w2_260 w2_25c w2_7c w2_64 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x1002
  obtain ⟨n4, c4, u4⟩ := s3.block svTrx1002 E3.self svTrx1002_end
    ⟨trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x1006 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svTrx1002 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_18 : reg n4 (18 : Fin 32) = out := by
    rw [rb4, runBlock_reg _ _ _ (18 : Fin 32) s3.zero (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by
    rw [rb4, runBlock_reg _ _ _ (20 : Fin 32) s3.zero (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by
    rw [rb4, runBlock_reg _ _ _ (21 : Fin 32) s3.zero (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by
    rw [rb4, runBlock_reg _ _ _ (22 : Fin 32) s3.zero (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by
    rw [rb4, runBlock_reg _ _ _ (23 : Fin 32) s3.zero (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = rem := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = x27 := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_10 : reg n4 a0 = aluEval .sltu 0 (dg) := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svTrx1002, upd, ↓reduceIte]; rw [g3_10, s3.zero]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m4]; exact w3_64
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m4]; exact w3_7c
  have w4_25c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m4]; exact w3_25c
  have w4_260 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m4]; exact w3_260
  have w4_264 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m4]; exact w3_264
  have w4_268 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m4]; exact w3_268
  have w4_378 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m4]; exact w3_378
  have w4_37c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m4]; exact w3_37c
  clear w3_37c w3_378 w3_268 w3_264 w3_260 w3_25c w3_7c w3_64 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x1006: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_1006 (off' := 0x1008) (by decide)
    (by rw [g4_2, show B + 0x21A0 + 0x7C = B + 0x21A0 + BitVec.ofNat 32 0x7C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0x1008 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_10 : reg n5 a0 = aluEval .sltu 0 (dg) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = rem := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
  have g5_11 : reg n5 a1 = flag := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_2, show B + 0x21A0 + 0x7C = B + 0x21A0 + BitVec.ofNat 32 0x7C by sv_addr, w4_7c]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m5]; exact w4_64
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m5]; exact w4_7c
  have w5_25c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m5]; exact w4_25c
  have w5_260 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m5]; exact w4_260
  have w5_264 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m5]; exact w4_264
  have w5_268 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m5]; exact w4_268
  have w5_378 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m5]; exact w4_378
  have w5_37c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m5]; exact w4_37c
  clear w4_37c w4_378 w4_268 w4_264 w4_260 w4_25c w4_7c w4_64 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x1008
  obtain ⟨n6, c6, u6⟩ := s5.block svTrx1008 E5.self svTrx1008_end
    ⟨trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x100A (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svTrx1008 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_11 : reg n6 a1 = flag := by
    rw [rb6, runBlock_reg _ _ _ a1 s5.zero (by decide), g5_11]
  have g6_18 : reg n6 (18 : Fin 32) = out := by
    rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by
    rw [rb6, runBlock_reg _ _ _ (20 : Fin 32) s5.zero (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by
    rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by
    rw [rb6, runBlock_reg _ _ _ (22 : Fin 32) s5.zero (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by
    rw [rb6, runBlock_reg _ _ _ (23 : Fin 32) s5.zero (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = rem := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_10 : reg n6 a0 = (aluEval .sltu 0 (dg)) &&& (flag) := by
    rw [rb6, ← g5_10, ← g5_11]; rfl
  have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m6]; exact w5_64
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m6]; exact w5_7c
  have w6_25c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m6]; exact w5_25c
  have w6_260 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m6]; exact w5_260
  have w6_264 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m6]; exact w5_264
  have w6_268 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m6]; exact w5_268
  have w6_378 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m6]; exact w5_378
  have w6_37c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m6]; exact w5_37c
  clear w5_37c w5_378 w5_268 w5_264 w5_260 w5_25c w5_7c w5_64 g5_11 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  by_cases hfl : dg ≠ 0 ∧ flag = 1
  rotate_left
  · -- 0x100A: branch, taken
    obtain ⟨n7, d7, u7⟩ := s6.taken E6.self 0x12B8 sv_at_100a
      (by decide) (by rw [g6_10, s6.zero]; exact br_beq_t ((snez_and_eq hflag).mpr hfl))
    have s7 : St n7.mem SV n7 0x12B8 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
    have g7_10 : reg n7 a0 = (aluEval .sltu 0 (dg)) &&& (flag) := by rw [u7.regs, g6_10]
    have g7_11 : reg n7 a1 = flag := by rw [u7.regs, g6_11]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = rem := by rw [u7.regs, g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [u7.regs, g6_27]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m7]; exact w6_64
    have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m7]; exact w6_7c
    have w7_25c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m7]; exact w6_25c
    have w7_260 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m7]; exact w6_260
    have w7_264 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m7]; exact w6_264
    have w7_268 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m7]; exact w6_268
    have w7_378 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m7]; exact w6_378
    have w7_37c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m7]; exact w6_37c
    clear w6_37c w6_378 w6_268 w6_264 w6_260 w6_25c w6_7c w6_64 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
    -- 0x12B8
    obtain ⟨n8, c8, u8⟩ := s7.block svTrx12b8 E7.self svTrx12b8_end
      ⟨trivial, trivial⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have s8 : St n8.mem SV n8 0x12BA (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have rb8 : ∀ q, reg n8 q = (runBlock svTrx12b8 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
    have g8_10 : reg n8 a0 = (aluEval .sltu 0 (dg)) &&& (flag) := by
      rw [rb8, runBlock_reg _ _ _ a0 s7.zero (by decide), g7_10]
    have g8_11 : reg n8 a1 = flag := by
      rw [rb8, runBlock_reg _ _ _ a1 s7.zero (by decide), g7_11]
    have g8_18 : reg n8 (18 : Fin 32) = out := by
      rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by
      rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = x20 := by
      rw [rb8, runBlock_reg _ _ _ (20 : Fin 32) s7.zero (by decide), g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by
      rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = x22 := by
      rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = x23 := by
      rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = rem := by
      rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = x25 := by
      rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = x26 := by
      rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = x27 := by
      rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
    have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb8]; simp +decide only [runBlock, BInstr.run, svTrx12b8, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_11, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk8 : SvKeepL B n0.mem n8.mem [] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m8]; exact w7_64
    have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m8]; exact w7_7c
    have w8_25c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m8]; exact w7_25c
    have w8_260 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m8]; exact w7_260
    have w8_264 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m8]; exact w7_264
    have w8_268 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m8]; exact w7_268
    have w8_378 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m8]; exact w7_378
    have w8_37c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m8]; exact w7_37c
    clear w7_37c w7_378 w7_268 w7_264 w7_260 w7_25c w7_7c w7_64 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_11 g7_10 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
    -- 0x12BA: j
    obtain ⟨n9, d9, u9⟩ := s8.jump E8.self sv_at_12ba (off' := 0x7A4) (by decide)
      (by rw [s8.pc]; decide)
    have s9 : St n9.mem SV n9 0x7A4 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u9.regs, g8_8]
    have g9_10 : reg n9 a0 = (aluEval .sltu 0 (dg)) &&& (flag) := by rw [u9.regs, g8_10]
    have g9_11 : reg n9 a1 = flag := by rw [u9.regs, g8_11]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = rem := by rw [u9.regs, g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [u9.regs, g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m9]; exact w8_64
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m9]; exact w8_7c
    have w9_25c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m9]; exact w8_25c
    have w9_260 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m9]; exact w8_260
    have w9_264 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m9]; exact w8_264
    have w9_268 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m9]; exact w8_268
    have w9_378 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m9]; exact w8_378
    have w9_37c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m9]; exact w8_37c
    clear w8_37c w8_378 w8_268 w8_264 w8_260 w8_25c w8_7c w8_64 g8_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_11 g8_10 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hfl h0'), sv_fail F E9 s9 t9 (fun x hx => (fR9 x hx).trans (fM x hx).symm) V9 hret g9_2 g9_18 hO g9_3 g9_4⟩
  -- 0x100A: branch, not taken
  obtain ⟨n7, d7, u7⟩ := s6.notTaken E6.self 0x100E sv_at_100a
    (by decide) (by rw [g6_10, s6.zero]; exact br_beq_f fun e => (snez_and_eq hflag).mp e hfl)
  have s7 : St n7.mem SV n7 0x100E (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
  have g7_10 : reg n7 a0 = (aluEval .sltu 0 (dg)) &&& (flag) := by rw [u7.regs, g6_10]
  have g7_11 : reg n7 a1 = flag := by rw [u7.regs, g6_11]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = rem := by rw [u7.regs, g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [u7.regs, g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m7]; exact w6_64
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m7]; exact w6_7c
  have w7_25c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m7]; exact w6_25c
  have w7_260 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m7]; exact w6_260
  have w7_264 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m7]; exact w6_264
  have w7_268 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m7]; exact w6_268
  have w7_378 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m7]; exact w6_378
  have w7_37c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m7]; exact w6_37c
  clear w6_37c w6_378 w6_268 w6_264 w6_260 w6_25c w6_7c w6_64 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0x100E
  obtain ⟨n8, c8, u8⟩ := s7.block svTrx100e E7.self svTrx100e_end
    ⟨trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x1014 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svTrx100e (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_18 : reg n8 (18 : Fin 32) = out := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by
    rw [rb8, runBlock_reg _ _ _ (20 : Fin 32) s7.zero (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by
    rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by
    rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by
    rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = rem := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by
    rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svTrx100e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_11, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_11 : reg n8 a1 = B + 0x21A0 + BitVec.ofNat 32 0x370 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svTrx100e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_11, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk8 : SvKeepL B n0.mem n8.mem [] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m8]; exact w7_64
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m8]; exact w7_7c
  have w8_25c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m8]; exact w7_25c
  have w8_260 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m8]; exact w7_260
  have w8_264 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m8]; exact w7_264
  have w8_268 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m8]; exact w7_268
  have w8_378 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m8]; exact w7_378
  have w8_37c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m8]; exact w7_37c
  clear w7_37c w7_378 w7_268 w7_264 w7_260 w7_25c w7_7c w7_64 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_11 g7_10 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x1014: sv_algF
  obtain ⟨n9, c9, s9, sp9, rk9, K9, A9, R9, fr9⟩ := sv_algF (oc := 0x420) (dc := 0x370) (nl := (sil).toNat)
    F E8 s8 sv_at_1014 sv_at_1018 (by decide) (by decide) g8_2 g8_10 g8_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w8_378 (by rw [w8_37c, ofNat_toNat_self]) si_in
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keepL K9 (by decide)
  rw [derAlgOf_congr (sv_pt fR8 si_in)] at R9
  rw [sv_mb fR8 si_in] at A9
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk9 (3 : Fin 32) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk9 (4 : Fin 32) (by decide), g8_4]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rk9 (18 : Fin 32) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rk9 (19 : Fin 32) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [rk9 (20 : Fin 32) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [rk9 (21 : Fin 32) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [rk9 (22 : Fin 32) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [rk9 (23 : Fin 32) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = rem := by rw [rk9 (24 : Fin 32) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [rk9 (25 : Fin 32) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [rk9 (26 : Fin 32) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [rk9 (27 : Fin 32) (by decide), g8_27]
  have g9_2 : reg n9 sp = B + 0x21A0 := sp9
  obtain ⟨r9, hr9⟩ : ∃ r, derAlgOf M0 (sip) ((sil).toNat) = r := ⟨_, rfl⟩
  rcases r9 with ab9 | ⟨⟨op9, ol9⟩, _ | ⟨prp9, pu9⟩⟩
  · rw [hr9] at R9
    obtain ⟨y0_9, -⟩ := R9
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x1C), (0x378, 0x8)] := keep_kk8.trans K9
    clear keep_kk8
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K9.w32 (by decide) (by decide)).trans w8_64
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K9.w32 (by decide) (by decide)).trans w8_7c
    have w9_25c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K9.w32 (by decide) (by decide)).trans w8_25c
    have w9_260 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K9.w32 (by decide) (by decide)).trans w8_260
    have w9_264 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K9.w32 (by decide) (by decide)).trans w8_264
    have w9_268 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K9.w32 (by decide) (by decide)).trans w8_268
    have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := y0_9
    clear w8_37c w8_378 w8_268 w8_264 w8_260 w8_25c w8_7c w8_64 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
    -- 0x101C: lw
    obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_101c (off' := 0x1020) (by decide)
      (by rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s10 : St n10.mem SV n10 0x1020 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = rem := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
    have g10_10 : reg n10 a0 = 0 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w9_420]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m10]; exact w9_64
    have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m10]; exact w9_7c
    have w10_25c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m10]; exact w9_25c
    have w10_260 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m10]; exact w9_260
    have w10_264 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m10]; exact w9_264
    have w10_268 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m10]; exact w9_268
    have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m10]; exact w9_420
    clear w9_420 w9_268 w9_264 w9_260 w9_25c w9_7c w9_64 y0_9
    -- 0x1020: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x12AA sv_at_1020
      (by decide) (by rw [g10_10, s10.zero]; rfl)
    have s11 : St n11.mem SV n11 0x12AA (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_10 : reg n11 a0 = 0 := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = rem := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m11]; exact w10_64
    have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m11]; exact w10_7c
    have w11_25c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m11]; exact w10_25c
    have w11_260 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m11]; exact w10_260
    have w11_264 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m11]; exact w10_264
    have w11_268 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m11]; exact w10_268
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m11]; exact w10_420
    clear w10_420 w10_268 w10_264 w10_260 w10_25c w10_7c w10_64 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x12AA: lbu
    obtain ⟨n12, d12, u12⟩ := s11.lbu E11.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s12 : St n12.mem SV n12 0x12AE (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
    have g12_10 : reg n12 a0 = 0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_10]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = rem := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m12]; exact w11_64
    have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m12]; exact w11_7c
    have w12_25c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m12]; exact w11_25c
    have w12_260 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m12]; exact w11_260
    have w12_264 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m12]; exact w11_264
    have w12_268 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m12]; exact w11_268
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m12]; exact w11_420
    clear w11_420 w11_268 w11_264 w11_260 w11_25c w11_7c w11_64 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    -- 0x12AE: j
    obtain ⟨n13, d13, u13⟩ := s12.jump E12.self sv_at_12ae (off' := 0x7A4) (by decide)
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
    have g13_10 : reg n13 a0 = 0 := by rw [u13.regs, g12_10]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = rem := by rw [u13.regs, g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, g12_27]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m13]; exact w12_64
    have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m13]; exact w12_7c
    have w13_25c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m13]; exact w12_25c
    have w13_260 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m13]; exact w12_260
    have w13_264 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m13]; exact w12_264
    have w13_268 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m13]; exact w12_268
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m13]; exact w12_420
    clear w12_420 w12_268 w12_264 w12_260 w12_25c w12_7c w12_64 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    exact .inl ⟨(fun ⟨h0', op9', ol9', h1', _⟩ => by rw [hr9] at h1'; cases h1'), sv_fail F E13 s13 t13 (fun x hx => (fR13 x hx).trans (fM x hx).symm) V13 hret g13_2 g13_18 hO g13_3 g13_4⟩
  rotate_left
  · rw [hr9] at R9
    obtain ⟨y0_9, y4_9, y8_9, -, -⟩ := R9
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x1C), (0x378, 0x8)] := keep_kk8.trans K9
    clear keep_kk8
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K9.w32 (by decide) (by decide)).trans w8_64
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K9.w32 (by decide) (by decide)).trans w8_7c
    have w9_25c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K9.w32 (by decide) (by decide)).trans w8_25c
    have w9_260 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K9.w32 (by decide) (by decide)).trans w8_260
    have w9_264 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K9.w32 (by decide) (by decide)).trans w8_264
    have w9_268 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K9.w32 (by decide) (by decide)).trans w8_268
    have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := y0_9
    have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := y4_9
    have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := y8_9
    clear w8_37c w8_378 w8_268 w8_264 w8_260 w8_25c w8_7c w8_64 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
    -- 0x101C: lw
    obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_101c (off' := 0x1020) (by decide)
      (by rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s10 : St n10.mem SV n10 0x1020 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = rem := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
    have g10_10 : reg n10 a0 = op9 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w9_420]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m10]; exact w9_64
    have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m10]; exact w9_7c
    have w10_25c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m10]; exact w9_25c
    have w10_260 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m10]; exact w9_260
    have w10_264 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m10]; exact w9_264
    have w10_268 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m10]; exact w9_268
    have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m10]; exact w9_420
    have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m10]; exact w9_424
    have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := by rw [m10]; exact w9_428
    clear w9_428 w9_424 w9_420 w9_268 w9_264 w9_260 w9_25c w9_7c w9_64 y8_9 y4_9 y0_9
    -- 0x1020: branch, not taken
    obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0x1024 sv_at_1020
      (by decide) (by rw [g10_10, s10.zero]; exact br_beq_f (si_in.algOid hr9).pos_ne)
    have s11 : St n11.mem SV n11 0x1024 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_10 : reg n11 a0 = op9 := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = rem := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m11]; exact w10_64
    have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m11]; exact w10_7c
    have w11_25c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m11]; exact w10_25c
    have w11_260 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m11]; exact w10_260
    have w11_264 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m11]; exact w10_264
    have w11_268 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m11]; exact w10_268
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m11]; exact w10_420
    have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m11]; exact w10_424
    have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := by rw [m11]; exact w10_428
    clear w10_428 w10_424 w10_420 w10_268 w10_264 w10_260 w10_25c w10_7c w10_64 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x1024: lw
    obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_1024 (off' := 0x1028) (by decide)
      (by rw [g11_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s12 : St n12.mem SV n12 0x1028 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
    have g12_10 : reg n12 a0 = op9 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_10]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = rem := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
    have g12_11 : reg n12 a1 = BitVec.ofNat 32 ol9 := by
      rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g11_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w11_424]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m12]; exact w11_64
    have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m12]; exact w11_7c
    have w12_25c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m12]; exact w11_25c
    have w12_260 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m12]; exact w11_260
    have w12_264 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m12]; exact w11_264
    have w12_268 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m12]; exact w11_268
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m12]; exact w11_420
    have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m12]; exact w11_424
    have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := by rw [m12]; exact w11_428
    clear w11_428 w11_424 w11_420 w11_268 w11_264 w11_260 w11_25c w11_7c w11_64 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    -- 0x1028: lw
    obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_1028 (off' := 0x102C) (by decide)
      (by rw [g12_2, show B + 0x21A0 + 0x428 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s13 : St n13.mem SV n13 0x102C (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
    have t13 : Steps n0 n13 := t12.trans (.single d13)
    have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
    have E13 : SvCode n13.mem := E12.fr F fr13
    have V13 : SvSaves B n13.mem v := V12.same m13
    have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
    have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
    have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
    have g13_10 : reg n13 a0 = op9 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_10]
    have g13_11 : reg n13 a1 = BitVec.ofNat 32 ol9 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_11]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = rem := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
    have g13_9 : reg n13 (9 : Fin 32) = prp9 + BitVec.ofNat 32 pu9.header := by
      rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g12_2, show B + 0x21A0 + 0x428 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w12_428]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m13]; exact w12_64
    have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m13]; exact w12_7c
    have w13_25c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m13]; exact w12_25c
    have w13_260 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m13]; exact w12_260
    have w13_264 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m13]; exact w12_264
    have w13_268 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m13]; exact w12_268
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m13]; exact w12_420
    have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m13]; exact w12_424
    have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := by rw [m13]; exact w12_428
    clear w12_428 w12_424 w12_420 w12_268 w12_264 w12_260 w12_25c w12_7c w12_64 g12_11 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    -- 0x102C
    obtain ⟨n14, c14, u14⟩ := s13.block svTrx102c E13.self svTrx102c_end
      ⟨trivial, trivial, trivial, trivial⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have s14 : St n14.mem SV n14 0x1036 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have rb14 : ∀ q, reg n14 q = (runBlock svTrx102c (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
    have g14_9 : reg n14 (9 : Fin 32) = prp9 + BitVec.ofNat 32 pu9.header := by
      rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
    have g14_10 : reg n14 a0 = op9 := by
      rw [rb14, runBlock_reg _ _ _ a0 s13.zero (by decide), g13_10]
    have g14_11 : reg n14 a1 = BitVec.ofNat 32 ol9 := by
      rw [rb14, runBlock_reg _ _ _ a1 s13.zero (by decide), g13_11]
    have g14_18 : reg n14 (18 : Fin 32) = out := by
      rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by
      rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
    have g14_20 : reg n14 (20 : Fin 32) = x20 := by
      rw [rb14, runBlock_reg _ _ _ (20 : Fin 32) s13.zero (by decide), g13_20]
    have g14_21 : reg n14 (21 : Fin 32) = x21 := by
      rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
    have g14_22 : reg n14 (22 : Fin 32) = x22 := by
      rw [rb14, runBlock_reg _ _ _ (22 : Fin 32) s13.zero (by decide), g13_22]
    have g14_23 : reg n14 (23 : Fin 32) = x23 := by
      rw [rb14, runBlock_reg _ _ _ (23 : Fin 32) s13.zero (by decide), g13_23]
    have g14_24 : reg n14 (24 : Fin 32) = rem := by
      rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = x25 := by
      rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = x26 := by
      rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = x27 := by
      rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
    have g14_12 : reg n14 a2 = BitVec.ofNat 32 (img% svConstAddress) := by
      rw [rb14]; simp +decide only [runBlock, BInstr.run, svTrx102c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g13_2, g13_3, g13_4, g13_9, g13_10, g13_11, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g14_13 : reg n14 a3 = BitVec.ofNat 32 0x8 := by
      rw [rb14]; simp +decide only [runBlock, BInstr.run, svTrx102c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g13_2, g13_3, g13_4, g13_9, g13_10, g13_11, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m14]; exact keep_kk13
    clear keep_kk13
    have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m14]; exact w13_64
    have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m14]; exact w13_7c
    have w14_25c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m14]; exact w13_25c
    have w14_260 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m14]; exact w13_260
    have w14_264 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m14]; exact w13_264
    have w14_268 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m14]; exact w13_268
    have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m14]; exact w13_420
    have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m14]; exact w13_424
    have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := by rw [m14]; exact w13_428
    clear w13_428 w13_424 w13_420 w13_268 w13_264 w13_260 w13_25c w13_7c w13_64 g13_9 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_11 g13_10 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
    -- 0x1036: sv_sneF
    obtain ⟨n15, c15, s15, rk15, a0_15, K15, fr15⟩ := sv_sneF (pl := ol9) (ql := 8)
      F E14 s14 sv_at_1036 sv_at_103a (by decide) (by decide) g14_2
      g14_10 g14_11 g14_12 g14_13 (.inl (si_in.algOid hr9)) (.inr ⟨by decide, by decide⟩)
    have t15 : Steps n0 n15 := t14.trans c15
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.keepL K15 (by decide)
    rw [sv_mbRo FW fR14 (.inl (si_in.algOid hr9)), sv_mbRo FW fR14 (.inr ⟨by decide, by decide⟩)] at a0_15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rk15 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk15 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk15 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_4]
    have g15_9 : reg n15 (9 : Fin 32) = prp9 + BitVec.ofNat 32 pu9.header := by rw [rk15 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_9]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rk15 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rk15 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_19]
    have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [rk15 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_20]
    have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [rk15 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [rk15 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [rk15 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = rem := by rw [rk15 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [rk15 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [rk15 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [rk15 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_27]
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x1C), (0x378, 0x8)] := keep_kk14.trans K15
    clear keep_kk14
    have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K15.w32 (by decide) (by decide)).trans w14_64
    have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K15.w32 (by decide) (by decide)).trans w14_7c
    have w15_25c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K15.w32 (by decide) (by decide)).trans w14_25c
    have w15_260 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K15.w32 (by decide) (by decide)).trans w14_260
    have w15_264 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K15.w32 (by decide) (by decide)).trans w14_264
    have w15_268 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K15.w32 (by decide) (by decide)).trans w14_268
    have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := (K15.w32 (by decide) (by decide)).trans w14_420
    have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := (K15.w32 (by decide) (by decide)).trans w14_424
    have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := (K15.w32 (by decide) (by decide)).trans w14_428
    clear w14_428 w14_424 w14_420 w14_268 w14_264 w14_260 w14_25c w14_7c w14_64 g14_13 g14_12 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_11 g14_10 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
    by_cases hoq : memBytes M0 op9 ol9 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress)) 8
    · have g15_10 : reg n15 a0 = BitVec.ofNat 32 0 := by rw [a0_15, ite_eq_left hoq]; rfl
      -- 0x103E
      obtain ⟨n16, c16, u16⟩ := s15.block svTrx103e E15.self svTrx103e_end
        ⟨trivial, trivial⟩
      have m16 : n16.mem = n15.mem := u16.mem
      have s16 : St n16.mem SV n16 0x1040 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
      have rb16 : ∀ q, reg n16 q = (runBlock svTrx103e (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
      have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
      have t16 : Steps n0 n16 := t15.trans c16
      have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
      have E16 : SvCode n16.mem := E15.fr F fr16
      have V16 : SvSaves B n16.mem v := V15.same m16
      have g16_2 : reg n16 sp = B + 0x21A0 := by
        rw [rb16, runBlock_reg _ _ _ sp s15.zero (by decide), g15_2]
      have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
        rw [rb16, runBlock_reg _ _ _ (3 : Fin 32) s15.zero (by decide), g15_3]
      have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
        rw [rb16, runBlock_reg _ _ _ (4 : Fin 32) s15.zero (by decide), g15_4]
      have g16_9 : reg n16 (9 : Fin 32) = prp9 + BitVec.ofNat 32 pu9.header := by
        rw [rb16, runBlock_reg _ _ _ (9 : Fin 32) s15.zero (by decide), g15_9]
      have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x0 := by
        rw [rb16, runBlock_reg _ _ _ a0 s15.zero (by decide), g15_10]
      have g16_18 : reg n16 (18 : Fin 32) = out := by
        rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
      have g16_19 : reg n16 (19 : Fin 32) = bp := by
        rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
      have g16_20 : reg n16 (20 : Fin 32) = x20 := by
        rw [rb16, runBlock_reg _ _ _ (20 : Fin 32) s15.zero (by decide), g15_20]
      have g16_21 : reg n16 (21 : Fin 32) = x21 := by
        rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
      have g16_22 : reg n16 (22 : Fin 32) = x22 := by
        rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
      have g16_23 : reg n16 (23 : Fin 32) = x23 := by
        rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
      have g16_24 : reg n16 (24 : Fin 32) = rem := by
        rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
      have g16_25 : reg n16 (25 : Fin 32) = x25 := by
        rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
      have g16_26 : reg n16 (26 : Fin 32) = x26 := by
        rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
      have g16_27 : reg n16 (27 : Fin 32) = x27 := by
        rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
      have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
        rw [rb16]; simp +decide only [runBlock, BInstr.run, svTrx103e, upd, ↓reduceIte, aluEval]
        all_goals (try simp only [g15_2, g15_3, g15_4, g15_9, g15_10, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
        all_goals first | with_reducible rfl | sv_addr | decide
      have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m16]; exact keep_kk15
      clear keep_kk15
      have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m16]; exact w15_64
      have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m16]; exact w15_7c
      have w16_25c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m16]; exact w15_25c
      have w16_260 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m16]; exact w15_260
      have w16_264 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m16]; exact w15_264
      have w16_268 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m16]; exact w15_268
      have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m16]; exact w15_420
      have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m16]; exact w15_424
      have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := by rw [m16]; exact w15_428
      clear w15_428 w15_424 w15_420 w15_268 w15_264 w15_260 w15_25c w15_7c w15_64 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 K15 a0_15 rk15 s15 c15
      -- 0x1040: branch, not taken
      obtain ⟨n17, d17, u17⟩ := s16.notTaken E16.self 0x1044 sv_at_1040
        (by decide) (by rw [g16_10, s16.zero]; decide)
      have s17 : St n17.mem SV n17 0x1044 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
      have m17 : n17.mem = n16.mem := u17.mem
      have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
      have t17 : Steps n0 n17 := t16.trans (.single d17)
      have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
      have E17 : SvCode n17.mem := E16.fr F fr17
      have V17 : SvSaves B n17.mem v := V16.same m17
      have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
      have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
      have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
      have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u17.regs, g16_8]
      have g17_9 : reg n17 (9 : Fin 32) = prp9 + BitVec.ofNat 32 pu9.header := by rw [u17.regs, g16_9]
      have g17_10 : reg n17 a0 = BitVec.ofNat 32 0x0 := by rw [u17.regs, g16_10]
      have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
      have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
      have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, g16_20]
      have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, g16_21]
      have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, g16_22]
      have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, g16_23]
      have g17_24 : reg n17 (24 : Fin 32) = rem := by rw [u17.regs, g16_24]
      have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, g16_25]
      have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, g16_26]
      have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [u17.regs, g16_27]
      have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m17]; exact keep_kk16
      clear keep_kk16
      have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m17]; exact w16_64
      have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m17]; exact w16_7c
      have w17_25c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m17]; exact w16_25c
      have w17_260 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m17]; exact w16_260
      have w17_264 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m17]; exact w16_264
      have w17_268 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m17]; exact w16_268
      have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m17]; exact w16_420
      have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m17]; exact w16_424
      have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := by rw [m17]; exact w16_428
      clear w16_428 w16_424 w16_420 w16_268 w16_264 w16_260 w16_25c w16_7c w16_64 g16_8 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_10 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16 g15_10
      -- 0x1044: branch, taken
      obtain ⟨n18, d18, u18⟩ := s17.taken E17.self 0x7A4 sv_at_1044
        (by decide) (by rw [g17_9, s17.zero]; exact br_bne_t (si_in.algParams hr9))
      have s18 : St n18.mem SV n18 0x7A4 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
      have m18 : n18.mem = n17.mem := u18.mem
      have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
      have t18 : Steps n0 n18 := t17.trans (.single d18)
      have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
      have E18 : SvCode n18.mem := E17.fr F fr18
      have V18 : SvSaves B n18.mem v := V17.same m18
      have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
      have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
      have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
      have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u18.regs, g17_8]
      have g18_9 : reg n18 (9 : Fin 32) = prp9 + BitVec.ofNat 32 pu9.header := by rw [u18.regs, g17_9]
      have g18_10 : reg n18 a0 = BitVec.ofNat 32 0x0 := by rw [u18.regs, g17_10]
      have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
      have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
      have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, g17_20]
      have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, g17_21]
      have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, g17_22]
      have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, g17_23]
      have g18_24 : reg n18 (24 : Fin 32) = rem := by rw [u18.regs, g17_24]
      have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, g17_25]
      have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, g17_26]
      have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [u18.regs, g17_27]
      have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m18]; exact keep_kk17
      clear keep_kk17
      have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m18]; exact w17_64
      have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m18]; exact w17_7c
      have w18_25c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m18]; exact w17_25c
      have w18_260 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m18]; exact w17_260
      have w18_264 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m18]; exact w17_264
      have w18_268 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m18]; exact w17_268
      have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m18]; exact w17_420
      have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m18]; exact w17_424
      have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := by rw [m18]; exact w17_428
      clear w17_428 w17_424 w17_420 w17_268 w17_264 w17_260 w17_25c w17_7c w17_64 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
      exact .inl ⟨(fun ⟨h0', op9', ol9', h1', _⟩ => by rw [hr9] at h1'; cases h1'), sv_fail F E18 s18 t18 (fun x hx => (fR18 x hx).trans (fM x hx).symm) V18 hret g18_2 g18_18 hO g18_3 g18_4⟩
    have g15_10 : reg n15 a0 = BitVec.ofNat 32 1 := by rw [a0_15, ite_eq_right hoq]; rfl
    -- 0x103E
    obtain ⟨n16, c16, u16⟩ := s15.block svTrx103e E15.self svTrx103e_end
      ⟨trivial, trivial⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have s16 : St n16.mem SV n16 0x1040 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have rb16 : ∀ q, reg n16 q = (runBlock svTrx103e (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans c16
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by
      rw [rb16, runBlock_reg _ _ _ sp s15.zero (by decide), g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb16, runBlock_reg _ _ _ (3 : Fin 32) s15.zero (by decide), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb16, runBlock_reg _ _ _ (4 : Fin 32) s15.zero (by decide), g15_4]
    have g16_9 : reg n16 (9 : Fin 32) = prp9 + BitVec.ofNat 32 pu9.header := by
      rw [rb16, runBlock_reg _ _ _ (9 : Fin 32) s15.zero (by decide), g15_9]
    have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb16, runBlock_reg _ _ _ a0 s15.zero (by decide), g15_10]
    have g16_18 : reg n16 (18 : Fin 32) = out := by
      rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by
      rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = x20 := by
      rw [rb16, runBlock_reg _ _ _ (20 : Fin 32) s15.zero (by decide), g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = x21 := by
      rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = x22 := by
      rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = x23 := by
      rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = rem := by
      rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by
      rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = x26 := by
      rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = x27 := by
      rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
    have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb16]; simp +decide only [runBlock, BInstr.run, svTrx103e, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g15_2, g15_3, g15_4, g15_9, g15_10, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m16]; exact w15_64
    have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m16]; exact w15_7c
    have w16_25c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m16]; exact w15_25c
    have w16_260 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m16]; exact w15_260
    have w16_264 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m16]; exact w15_264
    have w16_268 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m16]; exact w15_268
    have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m16]; exact w15_420
    have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m16]; exact w15_424
    have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := by rw [m16]; exact w15_428
    clear w15_428 w15_424 w15_420 w15_268 w15_264 w15_260 w15_25c w15_7c w15_64 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 K15 a0_15 rk15 s15 c15
    -- 0x1040: branch, taken
    obtain ⟨n17, d17, u17⟩ := s16.taken E16.self 0x7A4 sv_at_1040
      (by decide) (by rw [g16_10, s16.zero]; decide)
    have s17 : St n17.mem SV n17 0x7A4 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u17.regs, g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = prp9 + BitVec.ofNat 32 pu9.header := by rw [u17.regs, g16_9]
    have g17_10 : reg n17 a0 = BitVec.ofNat 32 0x1 := by rw [u17.regs, g16_10]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = rem := by rw [u17.regs, g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [u17.regs, g16_27]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m17]; exact w16_64
    have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m17]; exact w16_7c
    have w17_25c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m17]; exact w16_25c
    have w17_260 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m17]; exact w16_260
    have w17_264 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m17]; exact w16_264
    have w17_268 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m17]; exact w16_268
    have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m17]; exact w16_420
    have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m17]; exact w16_424
    have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = prp9 + BitVec.ofNat 32 pu9.header := by rw [m17]; exact w16_428
    clear w16_428 w16_424 w16_420 w16_268 w16_264 w16_260 w16_25c w16_7c w16_64 g16_8 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_10 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16 g15_10
    exact .inl ⟨(fun ⟨h0', op9', ol9', h1', _⟩ => by rw [hr9] at h1'; cases h1'), sv_fail F E17 s17 t17 (fun x hx => (fR17 x hx).trans (fM x hx).symm) V17 hret g17_2 g17_18 hO g17_3 g17_4⟩
  obtain ⟨te9, hte9⟩ := alg_ok_elem hr9
  obtain ⟨d8_9, d12_9⟩ := A9 te9 hte9
  rw [ofNat_toNat_self] at d12_9
  rw [hr9] at R9
  obtain ⟨y0_9, y4_9, y8_9⟩ := R9
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x1C), (0x378, 0x8)] := keep_kk8.trans K9
  clear keep_kk8
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K9.w32 (by decide) (by decide)).trans w8_64
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K9.w32 (by decide) (by decide)).trans w8_7c
  have w9_25c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K9.w32 (by decide) (by decide)).trans w8_25c
  have w9_260 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K9.w32 (by decide) (by decide)).trans w8_260
  have w9_264 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K9.w32 (by decide) (by decide)).trans w8_264
  have w9_268 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K9.w32 (by decide) (by decide)).trans w8_268
  have w9_378 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := d8_9
  have w9_37c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := d12_9
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := y0_9
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := y4_9
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := y8_9
  clear w8_37c w8_378 w8_268 w8_264 w8_260 w8_25c w8_7c w8_64 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0x101C: lw
  obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_101c (off' := 0x1020) (by decide)
    (by rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s10 : St n10.mem SV n10 0x1020 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = rem := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
  have g10_10 : reg n10 a0 = op9 := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w9_420]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m10]; exact w9_64
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m10]; exact w9_7c
  have w10_25c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m10]; exact w9_25c
  have w10_260 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m10]; exact w9_260
  have w10_264 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m10]; exact w9_264
  have w10_268 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m10]; exact w9_268
  have w10_378 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := by rw [m10]; exact w9_378
  have w10_37c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := by rw [m10]; exact w9_37c
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m10]; exact w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m10]; exact w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m10]; exact w9_428
  clear w9_428 w9_424 w9_420 w9_37c w9_378 w9_268 w9_264 w9_260 w9_25c w9_7c w9_64 y8_9 y4_9 y0_9 d12_9 d8_9 g9_2 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_4 g9_3 V9 E9 fR9 t9 fr9 A9 K9 rk9 sp9 s9 c9
  -- 0x1020: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0x1024 sv_at_1020
    (by decide) (by rw [g10_10, s10.zero]; exact br_beq_f (si_in.algOid hr9).pos_ne)
  have s11 : St n11.mem SV n11 0x1024 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_10 : reg n11 a0 = op9 := by rw [u11.regs, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = rem := by rw [u11.regs, g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m11]; exact w10_64
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m11]; exact w10_7c
  have w11_25c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m11]; exact w10_25c
  have w11_260 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m11]; exact w10_260
  have w11_264 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m11]; exact w10_264
  have w11_268 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m11]; exact w10_268
  have w11_378 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := by rw [m11]; exact w10_378
  have w11_37c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := by rw [m11]; exact w10_37c
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m11]; exact w10_428
  clear w10_428 w10_424 w10_420 w10_37c w10_378 w10_268 w10_264 w10_260 w10_25c w10_7c w10_64 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x1024: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_1024 (off' := 0x1028) (by decide)
    (by rw [g11_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x1028 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_10 : reg n12 a0 = op9 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_10]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = rem := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_11 : reg n12 a1 = BitVec.ofNat 32 ol9 := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w11_424]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m12]; exact w11_64
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m12]; exact w11_7c
  have w12_25c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m12]; exact w11_25c
  have w12_260 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m12]; exact w11_260
  have w12_264 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m12]; exact w11_264
  have w12_268 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m12]; exact w11_268
  have w12_378 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := by rw [m12]; exact w11_378
  have w12_37c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := by rw [m12]; exact w11_37c
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m12]; exact w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m12]; exact w11_428
  clear w11_428 w11_424 w11_420 w11_37c w11_378 w11_268 w11_264 w11_260 w11_25c w11_7c w11_64 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x1028: lw
  obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_1028 (off' := 0x102C) (by decide)
    (by rw [g12_2, show B + 0x21A0 + 0x428 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s13 : St n13.mem SV n13 0x102C (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_10 : reg n13 a0 = op9 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_10]
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 ol9 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_11]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = rem := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
  have g13_9 : reg n13 (9 : Fin 32) = 0 := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_2, show B + 0x21A0 + 0x428 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w12_428]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m13]; exact w12_64
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m13]; exact w12_7c
  have w13_25c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m13]; exact w12_25c
  have w13_260 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m13]; exact w12_260
  have w13_264 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m13]; exact w12_264
  have w13_268 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m13]; exact w12_268
  have w13_378 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := by rw [m13]; exact w12_378
  have w13_37c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := by rw [m13]; exact w12_37c
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m13]; exact w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m13]; exact w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m13]; exact w12_428
  clear w12_428 w12_424 w12_420 w12_37c w12_378 w12_268 w12_264 w12_260 w12_25c w12_7c w12_64 g12_11 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x102C
  obtain ⟨n14, c14, u14⟩ := s13.block svTrx102c E13.self svTrx102c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem SV n14 0x1036 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock svTrx102c (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_9 : reg n14 (9 : Fin 32) = 0 := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
  have g14_10 : reg n14 a0 = op9 := by
    rw [rb14, runBlock_reg _ _ _ a0 s13.zero (by decide), g13_10]
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 ol9 := by
    rw [rb14, runBlock_reg _ _ _ a1 s13.zero (by decide), g13_11]
  have g14_18 : reg n14 (18 : Fin 32) = out := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by
    rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by
    rw [rb14, runBlock_reg _ _ _ (20 : Fin 32) s13.zero (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by
    rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by
    rw [rb14, runBlock_reg _ _ _ (22 : Fin 32) s13.zero (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by
    rw [rb14, runBlock_reg _ _ _ (23 : Fin 32) s13.zero (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = rem := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by
    rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_12 : reg n14 a2 = BitVec.ofNat 32 (img% svConstAddress) := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTrx102c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_9, g13_10, g13_11, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g14_13 : reg n14 a3 = BitVec.ofNat 32 0x8 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTrx102c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_9, g13_10, g13_11, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m14]; exact w13_64
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m14]; exact w13_7c
  have w14_25c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m14]; exact w13_25c
  have w14_260 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m14]; exact w13_260
  have w14_264 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m14]; exact w13_264
  have w14_268 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m14]; exact w13_268
  have w14_378 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := by rw [m14]; exact w13_378
  have w14_37c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := by rw [m14]; exact w13_37c
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m14]; exact w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m14]; exact w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m14]; exact w13_428
  clear w13_428 w13_424 w13_420 w13_37c w13_378 w13_268 w13_264 w13_260 w13_25c w13_7c w13_64 g13_9 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_11 g13_10 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0x1036: sv_sneF
  obtain ⟨n15, c15, s15, rk15, a0_15, K15, fr15⟩ := sv_sneF (pl := ol9) (ql := 8)
    F E14 s14 sv_at_1036 sv_at_103a (by decide) (by decide) g14_2
    g14_10 g14_11 g14_12 g14_13 (.inl (si_in.algOid hr9)) (.inr ⟨by decide, by decide⟩)
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keepL K15 (by decide)
  rw [sv_mbRo FW fR14 (.inl (si_in.algOid hr9)), sv_mbRo FW fR14 (.inr ⟨by decide, by decide⟩)] at a0_15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rk15 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk15 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk15 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_4]
  have g15_9 : reg n15 (9 : Fin 32) = 0 := by rw [rk15 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rk15 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rk15 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [rk15 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [rk15 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [rk15 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [rk15 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = rem := by rw [rk15 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [rk15 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [rk15 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [rk15 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x1C), (0x378, 0x8)] := keep_kk14.trans K15
  clear keep_kk14
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K15.w32 (by decide) (by decide)).trans w14_64
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K15.w32 (by decide) (by decide)).trans w14_7c
  have w15_25c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K15.w32 (by decide) (by decide)).trans w14_25c
  have w15_260 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K15.w32 (by decide) (by decide)).trans w14_260
  have w15_264 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K15.w32 (by decide) (by decide)).trans w14_264
  have w15_268 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K15.w32 (by decide) (by decide)).trans w14_268
  have w15_378 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := (K15.w32 (by decide) (by decide)).trans w14_378
  have w15_37c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := (K15.w32 (by decide) (by decide)).trans w14_37c
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := (K15.w32 (by decide) (by decide)).trans w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := (K15.w32 (by decide) (by decide)).trans w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := (K15.w32 (by decide) (by decide)).trans w14_428
  clear w14_428 w14_424 w14_420 w14_37c w14_378 w14_268 w14_264 w14_260 w14_25c w14_7c w14_64 g14_13 g14_12 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_11 g14_10 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  by_cases hoid : memBytes M0 op9 ol9 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress)) 8
  rotate_left
  · have g15_10 : reg n15 a0 = BitVec.ofNat 32 1 := by rw [a0_15, ite_eq_right hoid]; rfl
    -- 0x103E
    obtain ⟨n16, c16, u16⟩ := s15.block svTrx103e E15.self svTrx103e_end
      ⟨trivial, trivial⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have s16 : St n16.mem SV n16 0x1040 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have rb16 : ∀ q, reg n16 q = (runBlock svTrx103e (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans c16
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by
      rw [rb16, runBlock_reg _ _ _ sp s15.zero (by decide), g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb16, runBlock_reg _ _ _ (3 : Fin 32) s15.zero (by decide), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb16, runBlock_reg _ _ _ (4 : Fin 32) s15.zero (by decide), g15_4]
    have g16_9 : reg n16 (9 : Fin 32) = 0 := by
      rw [rb16, runBlock_reg _ _ _ (9 : Fin 32) s15.zero (by decide), g15_9]
    have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb16, runBlock_reg _ _ _ a0 s15.zero (by decide), g15_10]
    have g16_18 : reg n16 (18 : Fin 32) = out := by
      rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by
      rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = x20 := by
      rw [rb16, runBlock_reg _ _ _ (20 : Fin 32) s15.zero (by decide), g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = x21 := by
      rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = x22 := by
      rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = x23 := by
      rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = rem := by
      rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by
      rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = x26 := by
      rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = x27 := by
      rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
    have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb16]; simp +decide only [runBlock, BInstr.run, svTrx103e, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g15_2, g15_3, g15_4, g15_9, g15_10, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m16]; exact w15_64
    have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m16]; exact w15_7c
    have w16_25c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m16]; exact w15_25c
    have w16_260 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m16]; exact w15_260
    have w16_264 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m16]; exact w15_264
    have w16_268 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m16]; exact w15_268
    have w16_378 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := by rw [m16]; exact w15_378
    have w16_37c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := by rw [m16]; exact w15_37c
    have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m16]; exact w15_420
    have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m16]; exact w15_424
    have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m16]; exact w15_428
    clear w15_428 w15_424 w15_420 w15_37c w15_378 w15_268 w15_264 w15_260 w15_25c w15_7c w15_64 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 K15 a0_15 rk15 s15 c15
    -- 0x1040: branch, taken
    obtain ⟨n17, d17, u17⟩ := s16.taken E16.self 0x7A4 sv_at_1040
      (by decide) (by rw [g16_10, s16.zero]; decide)
    have s17 : St n17.mem SV n17 0x7A4 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u17.regs, g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = 0 := by rw [u17.regs, g16_9]
    have g17_10 : reg n17 a0 = BitVec.ofNat 32 0x1 := by rw [u17.regs, g16_10]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = rem := by rw [u17.regs, g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [u17.regs, g16_27]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m17]; exact w16_64
    have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m17]; exact w16_7c
    have w17_25c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m17]; exact w16_25c
    have w17_260 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m17]; exact w16_260
    have w17_264 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m17]; exact w16_264
    have w17_268 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m17]; exact w16_268
    have w17_378 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := by rw [m17]; exact w16_378
    have w17_37c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := by rw [m17]; exact w16_37c
    have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m17]; exact w16_420
    have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m17]; exact w16_424
    have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m17]; exact w16_428
    clear w16_428 w16_424 w16_420 w16_37c w16_378 w16_268 w16_264 w16_260 w16_25c w16_7c w16_64 g16_8 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_10 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16 g15_10
    exact .inl ⟨(fun ⟨h0', op9', ol9', h1', te9', h2', h3', _⟩ => by rw [hr9] at h1'; cases h1'; rw [hte9] at h2'; cases h2'; exact hoid h3'), sv_fail F E17 s17 t17 (fun x hx => (fR17 x hx).trans (fM x hx).symm) V17 hret g17_2 g17_18 hO g17_3 g17_4⟩
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 0 := by rw [a0_15, ite_eq_left hoid]; rfl
  -- 0x103E
  obtain ⟨n16, c16, u16⟩ := s15.block svTrx103e E15.self svTrx103e_end
    ⟨trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem SV n16 0x1040 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock svTrx103e (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by
    rw [rb16, runBlock_reg _ _ _ sp s15.zero (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (3 : Fin 32) s15.zero (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (4 : Fin 32) s15.zero (by decide), g15_4]
  have g16_9 : reg n16 (9 : Fin 32) = 0 := by
    rw [rb16, runBlock_reg _ _ _ (9 : Fin 32) s15.zero (by decide), g15_9]
  have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb16, runBlock_reg _ _ _ a0 s15.zero (by decide), g15_10]
  have g16_18 : reg n16 (18 : Fin 32) = out := by
    rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by
    rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by
    rw [rb16, runBlock_reg _ _ _ (20 : Fin 32) s15.zero (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by
    rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by
    rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by
    rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = rem := by
    rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by
    rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by
    rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = x27 := by
    rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svTrx103e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_9, g15_10, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m16]; exact w15_64
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m16]; exact w15_7c
  have w16_25c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m16]; exact w15_25c
  have w16_260 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m16]; exact w15_260
  have w16_264 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m16]; exact w15_264
  have w16_268 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m16]; exact w15_268
  have w16_378 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := by rw [m16]; exact w15_378
  have w16_37c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := by rw [m16]; exact w15_37c
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m16]; exact w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m16]; exact w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m16]; exact w15_428
  clear w15_428 w15_424 w15_420 w15_37c w15_378 w15_268 w15_264 w15_260 w15_25c w15_7c w15_64 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 K15 a0_15 rk15 s15 c15
  -- 0x1040: branch, not taken
  obtain ⟨n17, d17, u17⟩ := s16.notTaken E16.self 0x1044 sv_at_1040
    (by decide) (by rw [g16_10, s16.zero]; decide)
  have s17 : St n17.mem SV n17 0x1044 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u17.regs, g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = 0 := by rw [u17.regs, g16_9]
  have g17_10 : reg n17 a0 = BitVec.ofNat 32 0x0 := by rw [u17.regs, g16_10]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = rem := by rw [u17.regs, g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [u17.regs, g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m17]; exact w16_64
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m17]; exact w16_7c
  have w17_25c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m17]; exact w16_25c
  have w17_260 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m17]; exact w16_260
  have w17_264 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m17]; exact w16_264
  have w17_268 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m17]; exact w16_268
  have w17_378 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := by rw [m17]; exact w16_378
  have w17_37c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := by rw [m17]; exact w16_37c
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m17]; exact w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m17]; exact w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m17]; exact w16_428
  clear w16_428 w16_424 w16_420 w16_37c w16_378 w16_268 w16_264 w16_260 w16_25c w16_7c w16_64 g16_8 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_10 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16 g15_10
  -- 0x1044: branch, not taken
  obtain ⟨n18, d18, u18⟩ := s17.notTaken E17.self 0x1048 sv_at_1044
    (by decide) (by rw [g17_9, s17.zero]; rfl)
  have s18 : St n18.mem SV n18 0x1048 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u18.regs, g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = 0 := by rw [u18.regs, g17_9]
  have g18_10 : reg n18 a0 = BitVec.ofNat 32 0x0 := by rw [u18.regs, g17_10]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = rem := by rw [u18.regs, g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [u18.regs, g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m18]; exact w17_64
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m18]; exact w17_7c
  have w18_25c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m18]; exact w17_25c
  have w18_260 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m18]; exact w17_260
  have w18_264 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m18]; exact w17_264
  have w18_268 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m18]; exact w17_268
  have w18_378 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := by rw [m18]; exact w17_378
  have w18_37c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := by rw [m18]; exact w17_37c
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m18]; exact w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m18]; exact w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m18]; exact w17_428
  clear w17_428 w17_424 w17_420 w17_37c w17_378 w17_268 w17_264 w17_260 w17_25c w17_7c w17_64 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0x1048
  obtain ⟨n19, c19, u19⟩ := s18.block svTrx1048 E18.self svTrx1048_end
    ⟨trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x104E (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svTrx1048 (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by
    rw [rb19, runBlock_reg _ _ _ sp s18.zero (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (3 : Fin 32) s18.zero (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (4 : Fin 32) s18.zero (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = 0 := by
    rw [rb19, runBlock_reg _ _ _ (9 : Fin 32) s18.zero (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by
    rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by
    rw [rb19, runBlock_reg _ _ _ (20 : Fin 32) s18.zero (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by
    rw [rb19, runBlock_reg _ _ _ (21 : Fin 32) s18.zero (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by
    rw [rb19, runBlock_reg _ _ _ (22 : Fin 32) s18.zero (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by
    rw [rb19, runBlock_reg _ _ _ (23 : Fin 32) s18.zero (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = rem := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by
    rw [rb19, runBlock_reg _ _ _ (25 : Fin 32) s18.zero (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svTrx1048, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_10, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0x370 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svTrx1048, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_10, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x1C), (0x378, 0x8)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m19]; exact w18_64
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m19]; exact w18_7c
  have w19_25c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m19]; exact w18_25c
  have w19_260 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m19]; exact w18_260
  have w19_264 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m19]; exact w18_264
  have w19_268 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m19]; exact w18_268
  have w19_378 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (sip) + BitVec.ofNat 32 (te9.header + te9.len) := by rw [m19]; exact w18_378
  have w19_37c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (sil) - BitVec.ofNat 32 (te9.header + te9.len) := by rw [m19]; exact w18_37c
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m19]; exact w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m19]; exact w18_428
  clear w18_428 w18_424 w18_420 w18_37c w18_378 w18_268 w18_264 w18_260 w18_25c w18_7c w18_64 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x104E: sv_octF
  obtain ⟨n20, c20, s20, sp20, rk20, K20, A20, Ok20, Er20, fr20⟩ := sv_octF (oc := 0x400) (dc := 0x370)
    F E19 s19 sv_at_104e sv_at_1052 (by decide) (by decide) g19_2 g19_10 g19_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w19_378 w19_37c (si_in.restW hte9)
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keepL K20 (by decide)
  rw [sv_mb fR19 (si_in.restW hte9)] at A20 Ok20 Er20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [rk20 sp (by decide) (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk20 (3 : Fin 32) (by decide) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk20 (4 : Fin 32) (by decide) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rk20 (8 : Fin 32) (by decide) (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = 0 := by rw [rk20 (9 : Fin 32) (by decide) (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rk20 (18 : Fin 32) (by decide) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rk20 (19 : Fin 32) (by decide) (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [rk20 (20 : Fin 32) (by decide) (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [rk20 (21 : Fin 32) (by decide) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [rk20 (22 : Fin 32) (by decide) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [rk20 (23 : Fin 32) (by decide) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = rem := by rw [rk20 (24 : Fin 32) (by decide) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [rk20 (25 : Fin 32) (by decide) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [rk20 (26 : Fin 32) (by decide) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [rk20 (27 : Fin 32) (by decide) (by decide), g19_27]
  obtain ⟨r20, hr20⟩ : ∃ r, derContent ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) (derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) ((sil) - BitVec.ofNat 32 (te9.header + te9.len)).toNat)) = r := ⟨_, rfl⟩
  rcases r20 with er20 | ⟨vp20, vl20⟩
  · obtain ⟨z20, -⟩ := Er20 er20 hr20
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8)] := keep_kk19.trans K20
    clear keep_kk19
    have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K20.w32 (by decide) (by decide)).trans w19_64
    have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K20.w32 (by decide) (by decide)).trans w19_7c
    have w20_25c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K20.w32 (by decide) (by decide)).trans w19_25c
    have w20_260 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K20.w32 (by decide) (by decide)).trans w19_260
    have w20_264 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K20.w32 (by decide) (by decide)).trans w19_264
    have w20_268 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K20.w32 (by decide) (by decide)).trans w19_268
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := (K20.w32 (by decide) (by decide)).trans w19_420
    have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := (K20.w32 (by decide) (by decide)).trans w19_424
    have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := (K20.w32 (by decide) (by decide)).trans w19_428
    have w20_400 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = 0 := z20
    clear w19_428 w19_424 w19_420 w19_37c w19_378 w19_268 w19_264 w19_260 w19_25c w19_7c w19_64 g19_11 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
    -- 0x1056: lw
    obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_1056 (off' := 0x105A) (by decide)
      (by rw [g20_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s21 : St n21.mem SV n21 0x105A (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
    have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_8]
    have g21_9 : reg n21 (9 : Fin 32) = 0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = rem := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
    have g21_11 : reg n21 a1 = 0 := by
      rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g20_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr, w20_400]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m21]; exact w20_64
    have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m21]; exact w20_7c
    have w21_25c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m21]; exact w20_25c
    have w21_260 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m21]; exact w20_260
    have w21_264 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m21]; exact w20_264
    have w21_268 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m21]; exact w20_268
    have w21_400 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = 0 := by rw [m21]; exact w20_400
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m21]; exact w20_420
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m21]; exact w20_424
    have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m21]; exact w20_428
    clear w20_400 w20_428 w20_424 w20_420 w20_268 w20_264 w20_260 w20_25c w20_7c w20_64 z20
    -- 0x105A: branch, taken
    obtain ⟨n22, d22, u22⟩ := s21.taken E21.self 0x1082 sv_at_105a
      (by decide) (by rw [g21_11, s21.zero]; rfl)
    have s22 : St n22.mem SV n22 0x1082 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u22.regs, g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = 0 := by rw [u22.regs, g21_9]
    have g22_11 : reg n22 a1 = 0 := by rw [u22.regs, g21_11]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = rem := by rw [u22.regs, g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m22]; exact w21_64
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m22]; exact w21_7c
    have w22_25c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m22]; exact w21_25c
    have w22_260 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m22]; exact w21_260
    have w22_264 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m22]; exact w21_264
    have w22_268 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m22]; exact w21_268
    have w22_400 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = 0 := by rw [m22]; exact w21_400
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m22]; exact w21_420
    have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m22]; exact w21_424
    have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m22]; exact w21_428
    clear w21_428 w21_424 w21_420 w21_400 w21_268 w21_264 w21_260 w21_25c w21_7c w21_64 g21_11 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
    -- 0x1082: lbu
    obtain ⟨n23, d23, u23⟩ := s22.lbu E22.self sv_at_1082 (off' := 0x1086) (by decide)
    have s23 : St n23.mem SV n23 0x1086 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
    have t23 : Steps n0 n23 := t22.trans (.single d23)
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.same m23
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
    have g23_9 : reg n23 (9 : Fin 32) = 0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
    have g23_11 : reg n23 a1 = 0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_11]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
    have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = rem := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m23]; exact w22_64
    have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m23]; exact w22_7c
    have w23_25c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m23]; exact w22_25c
    have w23_260 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m23]; exact w22_260
    have w23_264 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m23]; exact w22_264
    have w23_268 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m23]; exact w22_268
    have w23_400 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = 0 := by rw [m23]; exact w22_400
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m23]; exact w22_420
    have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m23]; exact w22_424
    have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m23]; exact w22_428
    clear w22_428 w22_424 w22_420 w22_400 w22_268 w22_264 w22_260 w22_25c w22_7c w22_64 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_11 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    -- 0x1086: j
    obtain ⟨n24, d24, u24⟩ := s23.jump E23.self sv_at_1086 (off' := 0x7A4) (by decide)
      (by rw [s23.pc]; decide)
    have s24 : St n24.mem SV n24 0x7A4 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
    have g24_9 : reg n24 (9 : Fin 32) = 0 := by rw [u24.regs, g23_9]
    have g24_11 : reg n24 a1 = 0 := by rw [u24.regs, g23_11]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = rem := by rw [u24.regs, g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [u24.regs, g23_27]
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m24]; exact w23_64
    have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m24]; exact w23_7c
    have w24_25c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m24]; exact w23_25c
    have w24_260 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m24]; exact w23_260
    have w24_264 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m24]; exact w23_264
    have w24_268 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m24]; exact w23_268
    have w24_400 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = 0 := by rw [m24]; exact w23_400
    have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m24]; exact w23_420
    have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m24]; exact w23_424
    have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m24]; exact w23_428
    clear w23_428 w23_424 w23_420 w23_400 w23_268 w23_264 w23_260 w23_25c w23_7c w23_64 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_11 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
    exact .inl ⟨(fun ⟨h0', op9', ol9', h1', te9', h2', h3', vp20', vl20', h4', _⟩ => by rw [hr9] at h1'; cases h1'; rw [hte9] at h2'; cases h2'; rw [hr20] at h4'; cases h4'), sv_fail F E24 s24 t24 (fun x hx => (fR24 x hx).trans (fM x hx).symm) V24 hret g24_2 g24_18 hO g24_3 g24_4⟩
  obtain ⟨te20, ht20, -, -⟩ := content_ok_elem hr20
  obtain ⟨p0_20, p4_20⟩ := Ok20 vp20 vl20 hr20
  obtain ⟨d8_20, d12_20⟩ := A20 te20 ht20
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8)] := keep_kk19.trans K20
  clear keep_kk19
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K20.w32 (by decide) (by decide)).trans w19_64
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K20.w32 (by decide) (by decide)).trans w19_7c
  have w20_25c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K20.w32 (by decide) (by decide)).trans w19_25c
  have w20_260 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K20.w32 (by decide) (by decide)).trans w19_260
  have w20_264 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K20.w32 (by decide) (by decide)).trans w19_264
  have w20_268 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K20.w32 (by decide) (by decide)).trans w19_268
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := (K20.w32 (by decide) (by decide)).trans w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := (K20.w32 (by decide) (by decide)).trans w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := (K20.w32 (by decide) (by decide)).trans w19_428
  have w20_378 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := d8_20
  have w20_37c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := d12_20
  have w20_400 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := p0_20
  have w20_404 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := p4_20
  clear w19_428 w19_424 w19_420 w19_37c w19_378 w19_268 w19_264 w19_260 w19_25c w19_7c w19_64 g19_11 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0x1056: lw
  obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_1056 (off' := 0x105A) (by decide)
    (by rw [g20_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s21 : St n21.mem SV n21 0x105A (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = 0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = rem := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
  have g21_11 : reg n21 a1 = vp20 := by
    rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g20_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr, w20_400]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m21]; exact w20_64
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m21]; exact w20_7c
  have w21_25c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m21]; exact w20_25c
  have w21_260 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m21]; exact w20_260
  have w21_264 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m21]; exact w20_264
  have w21_268 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m21]; exact w20_268
  have w21_378 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m21]; exact w20_378
  have w21_37c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m21]; exact w20_37c
  have w21_400 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m21]; exact w20_400
  have w21_404 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m21]; exact w20_404
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m21]; exact w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m21]; exact w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m21]; exact w20_428
  clear w20_404 w20_400 w20_37c w20_378 w20_428 w20_424 w20_420 w20_268 w20_264 w20_260 w20_25c w20_7c w20_64 d12_20 d8_20 p4_20 p0_20 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 Er20 Ok20 A20 K20 rk20 sp20 s20 c20
  -- 0x105A: branch, not taken
  obtain ⟨n22, d22, u22⟩ := s21.notTaken E21.self 0x105C sv_at_105a
    (by decide) (by rw [g21_11, s21.zero]; exact br_beq_f (((si_in.restW hte9).contentIn hr20).pos_ne))
  have s22 : St n22.mem SV n22 0x105C (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u22.regs, g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = 0 := by rw [u22.regs, g21_9]
  have g22_11 : reg n22 a1 = vp20 := by rw [u22.regs, g21_11]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = rem := by rw [u22.regs, g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m22]; exact w21_64
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m22]; exact w21_7c
  have w22_25c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m22]; exact w21_25c
  have w22_260 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m22]; exact w21_260
  have w22_264 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m22]; exact w21_264
  have w22_268 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m22]; exact w21_268
  have w22_378 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m22]; exact w21_378
  have w22_37c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m22]; exact w21_37c
  have w22_400 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m22]; exact w21_400
  have w22_404 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m22]; exact w21_404
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m22]; exact w21_428
  clear w21_428 w21_424 w21_420 w21_404 w21_400 w21_37c w21_378 w21_268 w21_264 w21_260 w21_25c w21_7c w21_64 g21_11 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0x105C: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_105c (off' := 0x1060) (by decide)
    (by rw [g22_2, show B + 0x21A0 + 0x404 = B + 0x21A0 + BitVec.ofNat 32 0x404 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s23 : St n23.mem SV n23 0x1060 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = 0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_11 : reg n23 a1 = vp20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_11]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = rem := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_12 : reg n23 a2 = vl20 := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_2, show B + 0x21A0 + 0x404 = B + 0x21A0 + BitVec.ofNat 32 0x404 by sv_addr, w22_404]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m23]; exact w22_64
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m23]; exact w22_7c
  have w23_25c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m23]; exact w22_25c
  have w23_260 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m23]; exact w22_260
  have w23_264 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m23]; exact w22_264
  have w23_268 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m23]; exact w22_268
  have w23_378 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m23]; exact w22_378
  have w23_37c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m23]; exact w22_37c
  have w23_400 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m23]; exact w22_400
  have w23_404 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m23]; exact w22_404
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m23]; exact w22_428
  clear w22_428 w22_424 w22_420 w22_404 w22_400 w22_37c w22_378 w22_268 w22_264 w22_260 w22_25c w22_7c w22_64 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_11 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0x1060
  obtain ⟨n24, c24, u24⟩ := s23.block svTrx1060 E23.self svTrx1060_end
    ⟨trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem SV n24 0x1064 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock svTrx1060 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = 0 := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
  have g24_11 : reg n24 a1 = vp20 := by
    rw [rb24, runBlock_reg _ _ _ a1 s23.zero (by decide), g23_11]
  have g24_12 : reg n24 a2 = vl20 := by
    rw [rb24, runBlock_reg _ _ _ a2 s23.zero (by decide), g23_12]
  have g24_18 : reg n24 (18 : Fin 32) = out := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by
    rw [rb24, runBlock_reg _ _ _ (20 : Fin 32) s23.zero (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by
    rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by
    rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by
    rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = rem := by
    rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by
    rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_10 : reg n24 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svTrx1060, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_11, g23_12, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m24]; exact w23_64
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m24]; exact w23_7c
  have w24_25c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m24]; exact w23_25c
  have w24_260 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m24]; exact w23_260
  have w24_264 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m24]; exact w23_264
  have w24_268 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m24]; exact w23_268
  have w24_378 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m24]; exact w23_378
  have w24_37c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m24]; exact w23_37c
  have w24_400 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m24]; exact w23_400
  have w24_404 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m24]; exact w23_404
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op9 := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ol9 := by rw [m24]; exact w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = 0 := by rw [m24]; exact w23_428
  clear w23_428 w23_424 w23_420 w23_404 w23_400 w23_37c w23_378 w23_268 w23_264 w23_260 w23_25c w23_7c w23_64 g23_12 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_11 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0x1064: sv_esF
  obtain ⟨n25, c25, s25, sp25, rk25, K25, R25, fr25⟩ := sv_esF (oc := 0x420) (nl := (vl20).toNat)
    F E24 s24 sv_at_1064 sv_at_1068 (by decide) (by decide) g24_2
    g24_10 g24_11 (by rw [g24_12, ofNat_toNat_self]) (by decide) ((si_in.restW hte9).contentIn hr20)
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keepL K25 (by decide)
  rw [ecdsaSigOf_congr (sv_pt fR24 ((si_in.restW hte9).contentIn hr20))] at R25
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk25 (3 : Fin 32) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk25 (4 : Fin 32) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rk25 (8 : Fin 32) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = 0 := by rw [rk25 (9 : Fin 32) (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rk25 (18 : Fin 32) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rk25 (19 : Fin 32) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [rk25 (20 : Fin 32) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rk25 (21 : Fin 32) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [rk25 (22 : Fin 32) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [rk25 (23 : Fin 32) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = rem := by rw [rk25 (24 : Fin 32) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rk25 (25 : Fin 32) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rk25 (26 : Fin 32) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = x27 := by rw [rk25 (27 : Fin 32) (by decide), g24_27]
  have g25_2 : reg n25 sp = B + 0x21A0 := sp25
  obtain ⟨r25, hr25⟩ : ∃ r, ecdsaSigOf 48 M0 (vp20) ((vl20).toNat) = r := ⟨_, rfl⟩
  rcases r25 with eb25 | ⟨sr25, ss25⟩
  · rw [hr25] at R25
    obtain ⟨y0_25, -⟩ := R25
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61)] := keep_kk24.trans K25
    clear keep_kk24
    have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K25.w32 (by decide) (by decide)).trans w24_64
    have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K25.w32 (by decide) (by decide)).trans w24_7c
    have w25_25c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K25.w32 (by decide) (by decide)).trans w24_25c
    have w25_260 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K25.w32 (by decide) (by decide)).trans w24_260
    have w25_264 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K25.w32 (by decide) (by decide)).trans w24_264
    have w25_268 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K25.w32 (by decide) (by decide)).trans w24_268
    have w25_378 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := (K25.w32 (by decide) (by decide)).trans w24_378
    have w25_37c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := (K25.w32 (by decide) (by decide)).trans w24_37c
    have w25_400 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := (K25.w32 (by decide) (by decide)).trans w24_400
    have w25_404 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := (K25.w32 (by decide) (by decide)).trans w24_404
    have b25_420 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := y0_25
    clear w24_428 w24_424 w24_420 w24_404 w24_400 w24_37c w24_378 w24_268 w24_264 w24_260 w24_25c w24_7c w24_64 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_12 g24_11 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
    -- 0x106C: lbu
    obtain ⟨n26, d26, u26⟩ := s25.lbu E25.self sv_at_106c (off' := 0x1070) (by decide)
    have s26 : St n26.mem SV n26 0x1070 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans (.single d26)
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = 0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
    have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
    have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
    have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = rem := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
    have g26_10 : reg n26 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g25_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b25_420]
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61)] := by rw [m26]; exact keep_kk25
    clear keep_kk25
    have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m26]; exact w25_64
    have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m26]; exact w25_7c
    have w26_25c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m26]; exact w25_25c
    have w26_260 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m26]; exact w25_260
    have w26_264 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m26]; exact w25_264
    have w26_268 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m26]; exact w25_268
    have w26_378 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m26]; exact w25_378
    have w26_37c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m26]; exact w25_37c
    have w26_400 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m26]; exact w25_400
    have w26_404 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m26]; exact w25_404
    have b26_420 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m26]; exact b25_420
    clear b25_420 w25_404 w25_400 w25_37c w25_378 w25_268 w25_264 w25_260 w25_25c w25_7c w25_64 y0_25
    -- 0x1070: lbu
    obtain ⟨n27, d27, u27⟩ := s26.lbu E26.self sv_at_1070 (off' := 0x1074) (by decide)
    have s27 : St n27.mem SV n27 0x1074 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = 0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
    have g27_10 : reg n27 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_10]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
    have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_20]
    have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = rem := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
    have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61)] := by rw [m27]; exact keep_kk26
    clear keep_kk26
    have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m27]; exact w26_64
    have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m27]; exact w26_7c
    have w27_25c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m27]; exact w26_25c
    have w27_260 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m27]; exact w26_260
    have w27_264 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m27]; exact w26_264
    have w27_268 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m27]; exact w26_268
    have w27_378 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m27]; exact w26_378
    have w27_37c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m27]; exact w26_37c
    have w27_400 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m27]; exact w26_400
    have w27_404 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m27]; exact w26_404
    have b27_420 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m27]; exact b26_420
    clear b26_420 w26_404 w26_400 w26_37c w26_378 w26_268 w26_264 w26_260 w26_25c w26_7c w26_64 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
    -- 0x1074: branch, not taken
    obtain ⟨n28, d28, u28⟩ := s27.notTaken E27.self 0x1076 sv_at_1074
      (by decide) (by rw [g27_10, s27.zero]; decide)
    have s28 : St n28.mem SV n28 0x1076 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u28.regs, g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = 0 := by rw [u28.regs, g27_9]
    have g28_10 : reg n28 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u28.regs, g27_10]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = rem := by rw [u28.regs, g27_24]
    have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [u28.regs, g27_27]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m28]; exact w27_64
    have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m28]; exact w27_7c
    have w28_25c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m28]; exact w27_25c
    have w28_260 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m28]; exact w27_260
    have w28_264 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m28]; exact w27_264
    have w28_268 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m28]; exact w27_268
    have w28_378 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m28]; exact w27_378
    have w28_37c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m28]; exact w27_37c
    have w28_400 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m28]; exact w27_400
    have w28_404 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m28]; exact w27_404
    have b28_420 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m28]; exact b27_420
    clear b27_420 w27_404 w27_400 w27_37c w27_378 w27_268 w27_264 w27_260 w27_25c w27_7c w27_64 g27_27 g27_26 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
    -- 0x1076
    obtain ⟨n29, c29, u29⟩ := s28.block svTrx1076 E28.self svTrx1076_end
      ⟨trivial, trivial⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have s29 : St n29.mem SV n29 0x1078 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have rb29 : ∀ q, reg n29 q = (runBlock svTrx1076 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
    have g29_9 : reg n29 (9 : Fin 32) = 0 := by
      rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
    have g29_10 : reg n29 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [rb29, runBlock_reg _ _ _ a0 s28.zero (by decide), g28_10]
    have g29_18 : reg n29 (18 : Fin 32) = out := by
      rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by
      rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = x20 := by
      rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = x21 := by
      rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = x22 := by
      rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = x23 := by
      rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = rem := by
      rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
    have g29_26 : reg n29 (26 : Fin 32) = x26 := by
      rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = x27 := by
      rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m29]; exact w28_64
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m29]; exact w28_7c
    have w29_25c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m29]; exact w28_25c
    have w29_260 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m29]; exact w28_260
    have w29_264 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m29]; exact w28_264
    have w29_268 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m29]; exact w28_268
    have w29_378 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m29]; exact w28_378
    have w29_37c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m29]; exact w28_37c
    have w29_400 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m29]; exact w28_400
    have w29_404 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m29]; exact w28_404
    have b29_420 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m29]; exact b28_420
    clear b28_420 w28_404 w28_400 w28_37c w28_378 w28_268 w28_264 w28_260 w28_25c w28_7c w28_64 g28_27 g28_26 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
    -- 0x1078: j
    obtain ⟨n30, d30, u30⟩ := s29.jump E29.self sv_at_1078 (off' := 0x7A4) (by decide)
      (by rw [s29.pc]; decide)
    have s30 : St n30.mem SV n30 0x7A4 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
    have g30_9 : reg n30 (9 : Fin 32) = 0 := by rw [u30.regs, g29_9]
    have g30_10 : reg n30 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u30.regs, g29_10]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [u30.regs, g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [u30.regs, g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [u30.regs, g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [u30.regs, g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = rem := by rw [u30.regs, g29_24]
    have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [u30.regs, g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = x27 := by rw [u30.regs, g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m30]; exact w29_64
    have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m30]; exact w29_7c
    have w30_25c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m30]; exact w29_25c
    have w30_260 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m30]; exact w29_260
    have w30_264 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m30]; exact w29_264
    have w30_268 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m30]; exact w29_268
    have w30_378 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m30]; exact w29_378
    have w30_37c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m30]; exact w29_37c
    have w30_400 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m30]; exact w29_400
    have w30_404 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m30]; exact w29_404
    have b30_420 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m30]; exact b29_420
    clear b29_420 w29_404 w29_400 w29_37c w29_378 w29_268 w29_264 w29_260 w29_25c w29_7c w29_64 g29_27 g29_26 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_10 g29_9 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
    exact .inl ⟨(fun ⟨h0', op9', ol9', h1', te9', h2', h3', vp20', vl20', h4', te20', h5', sr25', ss25', h6', _⟩ => by rw [hr9] at h1'; cases h1'; rw [hte9] at h2'; cases h2'; rw [hr20] at h4'; cases h4'; rw [ht20] at h5'; cases h5'; rw [hr25] at h6'; cases h6'), sv_fail F E30 s30 t30 (fun x hx => (fR30 x hx).trans (fM x hx).symm) V30 hret g30_2 g30_18 hO g30_3 g30_4⟩
  rw [hr25] at R25
  obtain ⟨y0_25, yr_25, ys_25⟩ := R25
  have q25_421 : ∀ j, j < 48 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0) := fun j hj => by rw [show 0x421 + j = 0x420 + 1 + j by omega]; exact yr_25 j hj
  have q25_451 : ∀ j, j < 48 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by rw [show 0x451 + j = 0x420 + 49 + j by omega]; exact ys_25 j hj
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61)] := keep_kk24.trans K25
  clear keep_kk24
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K25.w32 (by decide) (by decide)).trans w24_64
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K25.w32 (by decide) (by decide)).trans w24_7c
  have w25_25c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K25.w32 (by decide) (by decide)).trans w24_25c
  have w25_260 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K25.w32 (by decide) (by decide)).trans w24_260
  have w25_264 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K25.w32 (by decide) (by decide)).trans w24_264
  have w25_268 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K25.w32 (by decide) (by decide)).trans w24_268
  have w25_378 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := (K25.w32 (by decide) (by decide)).trans w24_378
  have w25_37c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := (K25.w32 (by decide) (by decide)).trans w24_37c
  have w25_400 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := (K25.w32 (by decide) (by decide)).trans w24_400
  have w25_404 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := (K25.w32 (by decide) (by decide)).trans w24_404
  have b25_420 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := y0_25
  clear w24_428 w24_424 w24_420 w24_404 w24_400 w24_37c w24_378 w24_268 w24_264 w24_260 w24_25c w24_7c w24_64 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_12 g24_11 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0x106C: lbu
  obtain ⟨n26, d26, u26⟩ := s25.lbu E25.self sv_at_106c (off' := 0x1070) (by decide)
  have s26 : St n26.mem SV n26 0x1070 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = 0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = rem := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_10 : reg n26 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b25_420]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m26]; exact w25_64
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m26]; exact w25_7c
  have w26_25c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m26]; exact w25_25c
  have w26_260 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m26]; exact w25_260
  have w26_264 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m26]; exact w25_264
  have w26_268 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m26]; exact w25_268
  have w26_378 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m26]; exact w25_378
  have w26_37c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m26]; exact w25_37c
  have w26_400 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m26]; exact w25_400
  have w26_404 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m26]; exact w25_404
  have b26_420 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m26]; exact b25_420
  have q26_421 : ∀ j, j < 48 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0) := fun j hj => by rw [m26]; exact q25_421 j hj
  have q26_451 : ∀ j, j < 48 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by rw [m26]; exact q25_451 j hj
  clear b25_420 w25_404 w25_400 w25_37c w25_378 w25_268 w25_264 w25_260 w25_25c w25_7c w25_64 q25_451 q25_421 ys_25 yr_25 y0_25 g25_2 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 V25 E25 fR25 t25 fr25 K25 rk25 sp25 s25 c25
  -- 0x1070: lbu
  have b26_421 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 ((sr25).getD 0 0) := q26_421 0 (by decide)
  obtain ⟨n27, d27, u27⟩ := s26.lbu E26.self sv_at_1070 (off' := 0x1074) (by decide)
  have s27 : St n27.mem SV n27 0x1074 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = 0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
  have g27_10 : reg n27 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_10]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = rem := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
  have g27_25 : reg n27 (25 : Fin 32) = (BitVec.ofNat 8 ((sr25).getD 0 0)).zeroExtend 32 := by
    rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g26_2, show B + 0x21A0 + 0x421 = B + 0x21A0 + BitVec.ofNat 32 0x421 by sv_addr, b26_421]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m27]; exact w26_64
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m27]; exact w26_7c
  have w27_25c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m27]; exact w26_25c
  have w27_260 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m27]; exact w26_260
  have w27_264 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m27]; exact w26_264
  have w27_268 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m27]; exact w26_268
  have w27_378 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m27]; exact w26_378
  have w27_37c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m27]; exact w26_37c
  have w27_400 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m27]; exact w26_400
  have w27_404 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m27]; exact w26_404
  have b27_420 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m27]; exact b26_420
  have b27_421 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 ((sr25).getD 0 0) := by rw [m27]; exact b26_421
  have q27_421 : ∀ j, j < 48 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0) := fun j hj => by rw [m27]; exact q26_421 j hj
  have q27_451 : ∀ j, j < 48 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by rw [m27]; exact q26_451 j hj
  clear q26_451 q26_421 b26_420 w26_404 w26_400 w26_37c w26_378 w26_268 w26_264 w26_260 w26_25c w26_7c w26_64 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0x1074: branch, taken
  obtain ⟨n28, d28, u28⟩ := s27.taken E27.self 0x108A sv_at_1074
    (by decide) (by rw [g27_10, s27.zero]; decide)
  have s28 : St n28.mem SV n28 0x108A (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u28.regs, g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = 0 := by rw [u28.regs, g27_9]
  have g28_10 : reg n28 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u28.regs, g27_10]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = rem := by rw [u28.regs, g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = (BitVec.ofNat 8 ((sr25).getD 0 0)).zeroExtend 32 := by rw [u28.regs, g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [u28.regs, g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m28]; exact w27_64
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m28]; exact w27_7c
  have w28_25c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m28]; exact w27_25c
  have w28_260 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m28]; exact w27_260
  have w28_264 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m28]; exact w27_264
  have w28_268 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m28]; exact w27_268
  have w28_378 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m28]; exact w27_378
  have w28_37c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m28]; exact w27_37c
  have w28_400 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m28]; exact w27_400
  have w28_404 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m28]; exact w27_404
  have b28_420 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m28]; exact b27_420
  have b28_421 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 ((sr25).getD 0 0) := by rw [m28]; exact b27_421
  have q28_421 : ∀ j, j < 48 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0) := fun j hj => by rw [m28]; exact q27_421 j hj
  have q28_451 : ∀ j, j < 48 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by rw [m28]; exact q27_451 j hj
  clear q27_451 q27_421 b27_421 b27_420 w27_404 w27_400 w27_37c w27_378 w27_268 w27_264 w27_260 w27_25c w27_7c w27_64 g27_25 g27_27 g27_26 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27 b26_421
  -- 0x108A
  obtain ⟨n29, c29, u29⟩ := s28.block svTrx108a E28.self svTrx108a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem SV n29 0x1094 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock svTrx108a (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = 0 := by
    rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = out := by
    rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by
    rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by
    rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by
    rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by
    rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by
    rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = rem := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = (BitVec.ofNat 8 ((sr25).getD 0 0)).zeroExtend 32 := by
    rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = x27 := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_10 : reg n29 a0 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svTrx108a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_11 : reg n29 a1 = B + 0x21A0 + BitVec.ofNat 32 0x422 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svTrx108a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_12 : reg n29 a2 = BitVec.ofNat 32 0x5F := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svTrx108a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m29]; exact w28_64
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m29]; exact w28_7c
  have w29_25c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m29]; exact w28_25c
  have w29_260 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m29]; exact w28_260
  have w29_264 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m29]; exact w28_264
  have w29_268 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m29]; exact w28_268
  have w29_378 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m29]; exact w28_378
  have w29_37c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m29]; exact w28_37c
  have w29_400 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m29]; exact w28_400
  have w29_404 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m29]; exact w28_404
  have b29_420 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m29]; exact b28_420
  have b29_421 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 ((sr25).getD 0 0) := by rw [m29]; exact b28_421
  have q29_421 : ∀ j, j < 48 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0) := fun j hj => by rw [m29]; exact q28_421 j hj
  have q29_451 : ∀ j, j < 48 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by rw [m29]; exact q28_451 j hj
  clear q28_451 q28_421 b28_421 b28_420 w28_404 w28_400 w28_37c w28_378 w28_268 w28_264 w28_260 w28_25c w28_7c w28_64 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  -- 0x1094: memcpy
  obtain ⟨n30, P30, K30, X30⟩ := sv_mc (c := 0x380) (d := 0x422) (N := 0x5F) F E29 s29 sv_at_1094 sv_at_1098
    (by decide) (by decide) g29_2 g29_10 g29_11 g29_12
    (by decide) (by decide) (by decide)
  have s30 := P30.st
  have fr30 := P30.fr
  have t30 : Steps n0 n30 := t29.trans P30.steps
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keep K30 (by decide)
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [P30.regs sp (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P30.regs (3 : Fin 32) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P30.regs (4 : Fin 32) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [P30.regs (8 : Fin 32) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = 0 := by rw [P30.regs (9 : Fin 32) (by decide), g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [P30.regs (18 : Fin 32) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [P30.regs (19 : Fin 32) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [P30.regs (20 : Fin 32) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [P30.regs (21 : Fin 32) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [P30.regs (22 : Fin 32) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [P30.regs (23 : Fin 32) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = rem := by rw [P30.regs (24 : Fin 32) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = (BitVec.ofNat 8 ((sr25).getD 0 0)).zeroExtend 32 := by rw [P30.regs (25 : Fin 32) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [P30.regs (26 : Fin 32) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = x27 := by rw [P30.regs (27 : Fin 32) (by decide), g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61), (0x380, 0x5F)] := keep_kk29.trans K30.toL
  clear keep_kk29
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K30.w32 (by decide) (by decide)).trans w29_64
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K30.w32 (by decide) (by decide)).trans w29_7c
  have w30_25c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K30.w32 (by decide) (by decide)).trans w29_25c
  have w30_260 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K30.w32 (by decide) (by decide)).trans w29_260
  have w30_264 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K30.w32 (by decide) (by decide)).trans w29_264
  have w30_268 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K30.w32 (by decide) (by decide)).trans w29_268
  have w30_378 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := (K30.w32 (by decide) (by decide)).trans w29_378
  have w30_37c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := (K30.w32 (by decide) (by decide)).trans w29_37c
  have w30_400 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := (K30.w32 (by decide) (by decide)).trans w29_400
  have w30_404 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := (K30.w32 (by decide) (by decide)).trans w29_404
  have b30_420 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := (K30.b8 (by decide) (by decide)).trans b29_420
  have b30_421 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 ((sr25).getD 0 0) := (K30.b8 (by decide) (by decide)).trans b29_421
  have q30_421 : ∀ j, j < 48 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_421 j hj)
  have q30_451 : ∀ j, j < 48 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_451 j hj)
  have q30_380 : ∀ j, j < 47 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 ((sr25).getD (1 + j) 0) := fun j hj => by
    rw [show 0x380 + j = 0x380 + (0x0 + j) by omega, X30 (0x0 + j) (by omega),
      show 0x422 + (0x0 + j) = 0x421 + (1 + j) by omega]; exact q29_421 (1 + j) (by omega)
  have q30_3af : ∀ j, j < 48 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by
    rw [show 0x3AF + j = 0x380 + (0x2F + j) by omega, X30 (0x2F + j) (by omega),
      show 0x422 + (0x2F + j) = 0x451 + j by omega]; exact q29_451 j (by omega)
  clear q29_451 q29_421 b29_421 b29_420 w29_404 w29_400 w29_37c w29_378 w29_268 w29_264 w29_260 w29_25c w29_7c w29_64 g29_12 g29_11 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
  -- 0x109C: lw
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_109c (off' := 0x10A0) (by decide)
    (by rw [g30_2, show B + 0x21A0 + 0x37C = B + 0x21A0 + BitVec.ofNat 32 0x37C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s31 : St n31.mem SV n31 0x10A0 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = 0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = rem := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = (BitVec.ofNat 8 ((sr25).getD 0 0)).zeroExtend 32 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = x27 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
  have g31_10 : reg n31 a0 = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_2, show B + 0x21A0 + 0x37C = B + 0x21A0 + BitVec.ofNat 32 0x37C by sv_addr, w30_37c]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61), (0x380, 0x5F)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m31]; exact w30_64
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m31]; exact w30_7c
  have w31_25c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m31]; exact w30_25c
  have w31_260 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m31]; exact w30_260
  have w31_264 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m31]; exact w30_264
  have w31_268 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m31]; exact w30_268
  have w31_378 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m31]; exact w30_378
  have w31_37c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m31]; exact w30_37c
  have w31_400 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m31]; exact w30_400
  have w31_404 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m31]; exact w30_404
  have b31_420 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m31]; exact b30_420
  have b31_421 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 ((sr25).getD 0 0) := by rw [m31]; exact b30_421
  have q31_380 : ∀ j, j < 47 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 ((sr25).getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_380 j hj
  have q31_3af : ∀ j, j < 48 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by rw [m31]; exact q30_3af j hj
  have q31_421 : ∀ j, j < 48 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0) := fun j hj => by rw [m31]; exact q30_421 j hj
  have q31_451 : ∀ j, j < 48 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by rw [m31]; exact q30_451 j hj
  clear q30_3af q30_380 q30_451 q30_421 b30_421 b30_420 w30_404 w30_400 w30_37c w30_378 w30_268 w30_264 w30_260 w30_25c w30_7c w30_64 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 s30 X30 K30 P30
  by_cases hsi0 : ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) = 0
  rotate_left
  · -- 0x10A0: branch, taken
    obtain ⟨n32, d32, u32⟩ := s31.taken E31.self 0x7A4 sv_at_10a0
      (by decide) (by rw [g31_10, s31.zero]; exact br_bne_t hsi0)
    have s32 : St n32.mem SV n32 0x7A4 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
    have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u32.regs, g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = 0 := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [u32.regs, g31_10]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = rem := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = (BitVec.ofNat 8 ((sr25).getD 0 0)).zeroExtend 32 := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = x27 := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61), (0x380, 0x5F)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m32]; exact w31_64
    have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m32]; exact w31_7c
    have w32_25c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m32]; exact w31_25c
    have w32_260 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m32]; exact w31_260
    have w32_264 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m32]; exact w31_264
    have w32_268 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m32]; exact w31_268
    have w32_378 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m32]; exact w31_378
    have w32_37c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m32]; exact w31_37c
    have w32_400 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m32]; exact w31_400
    have w32_404 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m32]; exact w31_404
    have b32_420 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m32]; exact b31_420
    have b32_421 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 ((sr25).getD 0 0) := by rw [m32]; exact b31_421
    have q32_380 : ∀ j, j < 47 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 ((sr25).getD (1 + j) 0) := fun j hj => by rw [m32]; exact q31_380 j hj
    have q32_3af : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by rw [m32]; exact q31_3af j hj
    have q32_421 : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0) := fun j hj => by rw [m32]; exact q31_421 j hj
    have q32_451 : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by rw [m32]; exact q31_451 j hj
    clear q31_451 q31_421 q31_3af q31_380 b31_421 b31_420 w31_404 w31_400 w31_37c w31_378 w31_268 w31_264 w31_260 w31_25c w31_7c w31_64 g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    exact .inl ⟨(fun ⟨h0', op9', ol9', h1', te9', h2', h3', vp20', vl20', h4', te20', h5', sr25', ss25', h6', h7', _⟩ => by rw [hr9] at h1'; cases h1'; rw [hte9] at h2'; cases h2'; rw [hr20] at h4'; cases h4'; rw [ht20] at h5'; cases h5'; rw [hr25] at h6'; cases h6'; exact hsi0 h7'), sv_fail F E32 s32 t32 (fun x hx => (fR32 x hx).trans (fM x hx).symm) V32 hret g32_2 g32_18 hO g32_3 g32_4⟩
  -- 0x10A0: branch, not taken
  obtain ⟨n32, d32, u32⟩ := s31.notTaken E31.self 0x10A4 sv_at_10a0
    (by decide) (by rw [g31_10, s31.zero]; exact br_bne_f hsi0)
  have s32 : St n32.mem SV n32 0x10A4 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u32.regs, g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = 0 := by rw [u32.regs, g31_9]
  have g32_10 : reg n32 a0 = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [u32.regs, g31_10]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [u32.regs, g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = rem := by rw [u32.regs, g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = (BitVec.ofNat 8 ((sr25).getD 0 0)).zeroExtend 32 := by rw [u32.regs, g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = x27 := by rw [u32.regs, g31_27]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61), (0x380, 0x5F)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m32]; exact w31_64
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m32]; exact w31_7c
  have w32_25c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m32]; exact w31_25c
  have w32_260 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m32]; exact w31_260
  have w32_264 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m32]; exact w31_264
  have w32_268 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m32]; exact w31_268
  have w32_378 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m32]; exact w31_378
  have w32_37c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m32]; exact w31_37c
  have w32_400 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = vp20 := by rw [m32]; exact w31_400
  have w32_404 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = vl20 := by rw [m32]; exact w31_404
  have b32_420 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m32]; exact b31_420
  have b32_421 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 ((sr25).getD 0 0) := by rw [m32]; exact b31_421
  have q32_380 : ∀ j, j < 47 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 ((sr25).getD (1 + j) 0) := fun j hj => by rw [m32]; exact q31_380 j hj
  have q32_3af : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by rw [m32]; exact q31_3af j hj
  have q32_421 : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0) := fun j hj => by rw [m32]; exact q31_421 j hj
  have q32_451 : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0) := fun j hj => by rw [m32]; exact q31_451 j hj
  clear q31_451 q31_421 q31_3af q31_380 b31_421 b31_420 w31_404 w31_400 w31_37c w31_378 w31_268 w31_264 w31_260 w31_25c w31_7c w31_64 g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  exact .inr ⟨hfl, op9, ol9, hr9, te9, hte9, hoid, vp20, vl20, hr20, te20, ht20, sr25, ss25, hr25, hsi0, n32, t32, s32, E32, V32, fR32, g32_2, g32_3, g32_4, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, q32_380, q32_3af, q32_421, q32_451, keep_kk32.mono (by decide)⟩

end C3.RV32.Sv
