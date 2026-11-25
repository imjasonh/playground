import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: a signed attribute's type

One signed attribute, from the loop head at 0xEA0 to 0xF5C: a sequence of an OID and a set with nothing after it, whose OID no earlier attribute has.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTra107c : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x6]
theorem svTra107c_end : blockEnd sigstoreVerifyCode 0x107C svTra107c = some 0x107E := by
  simp only [svTra107c]
  rw [blockEnd, sv_at_107c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTraeae : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x25C]
theorem svTraeae_end : blockEnd sigstoreVerifyCode 0xEAE svTraeae = some 0xEB4 := by
  simp only [svTraeae]
  rw [blockEnd, sv_at_eae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_eb2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTraec8 : List BInstr :=
  [.aluImm .add a2 x0 0xB, .aluImm .add a0 sp 0x3E5, .aluImm .add a1 sp 0x425]
theorem svTraec8_end : blockEnd sigstoreVerifyCode 0xEC8 svTraec8 = some 0xED2 := by
  simp only [svTraec8]
  rw [blockEnd, sv_at_ec8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_eca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_ece]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTraee2 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x3E0]
theorem svTraee2_end : blockEnd sigstoreVerifyCode 0xEE2 svTraee2 = some 0xEE8 := by
  simp only [svTraee2]
  rw [blockEnd, sv_at_ee2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_ee6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTraefc : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x3E0]
theorem svTraefc_end : blockEnd sigstoreVerifyCode 0xEFC svTraefc = some 0xF02 := by
  simp only [svTraefc]
  rw [blockEnd, sv_at_efc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f00]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTraf16 : List BInstr :=
  [.aluImm .add a2 x0 0xB, .aluImm .add a0 sp 0x405, .aluImm .add a1 sp 0x425]
theorem svTraf16_end : blockEnd sigstoreVerifyCode 0xF16 svTraf16 = some 0xF20 := by
  simp only [svTraf16]
  rw [blockEnd, sv_at_f16]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f18]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f1c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTra14c : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x1]
theorem svTra14c_end : blockEnd sigstoreVerifyCode 0x14C svTra14c = some 0x14E := by
  simp only [svTra14c]
  rw [blockEnd, sv_at_14c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTraf38 : List BInstr :=
  [.alu .sub a1 (27 : Fin 32) (24 : Fin 32)]
theorem svTraf38_end : blockEnd sigstoreVerifyCode 0xF38 svTraf38 = some 0xF3C := by
  simp only [svTraf38]
  rw [blockEnd, sv_at_f38]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTraf3e : List BInstr :=
  [.alu .add a2 x0 (9 : Fin 32), .alu .add a3 x0 (26 : Fin 32)]
theorem svTraf3e_end : blockEnd sigstoreVerifyCode 0xF3E svTraf3e = some 0xF42 := by
  simp only [svTraf3e]
  rw [blockEnd, sv_at_f3e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f40]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTraf4a : List BInstr :=
  [.aluImm .and a0 a0 0x1, .alu .add (8 : Fin 32) x0 a1]
theorem svTraf4a_end : blockEnd sigstoreVerifyCode 0xF4A svTraf4a = some 0xF4E := by
  simp only [svTraf4a]
  rw [blockEnd, sv_at_f4a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f4c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTraf52 : List BInstr :=
  [.aluImm .and a0 (8 : Fin 32) 0x1, .aluImm .add (8 : Fin 32) x0 0x18]
theorem svTraf52_end : blockEnd sigstoreVerifyCode 0xF52 svTraf52 = some 0xF58 := by
  simp only [svTraf52]
  rw [blockEnd, sv_at_f52]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f56]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tra {B out bp x20 x21 x22 x23 x25 dg flag p0 L0 cp rem : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xEA0 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = rem)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag)
    (w0_25c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0)
    (w0_260 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0)
    (w0_264 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp)
    (w0_268 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem)
    (cr_in : SvIn B (cp) (rem).toNat)
    (p0_in : SvIn B (p0) (L0).toNat) :
    (¬ (((rem).toNat ≤ (L0).toNat) ∧ ∃ tl6, derElement 0x30 (memBytes M0 (cp) (rem).toNat) = .ok tl6 ∧ ∃ op15 ol15, derContent ((cp) + BitVec.ofNat 32 tl6.header) (derOid (memBytes M0 ((cp) + BitVec.ofNat 32 tl6.header) (BitVec.ofNat 32 tl6.len).toNat)) = .ok (op15, ol15) ∧ ∃ to15, derOid (memBytes M0 ((cp) + BitVec.ofNat 32 tl6.header) (BitVec.ofNat 32 tl6.len).toNat) = .ok to15 ∧ ∃ tl20, derElement 0x31 (memBytes M0 (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)).toNat) = .ok tl20 ∧ (((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) = 0) ∧ listsOidOf M0 p0 ((L0) - (rem)).toNat (memBytes M0 op15 ol15.toNat) = .ok false ∧ True) ∧ SvErrRet B out v n0) ∨
    (((rem).toNat ≤ (L0).toNat) ∧
    ∃ tl6, derElement 0x30 (memBytes M0 (cp) (rem).toNat) = .ok tl6 ∧
    ∃ op15 ol15, derContent ((cp) + BitVec.ofNat 32 tl6.header) (derOid (memBytes M0 ((cp) + BitVec.ofNat 32 tl6.header) (BitVec.ofNat 32 tl6.len).toNat)) = .ok (op15, ol15) ∧
    ∃ to15, derOid (memBytes M0 ((cp) + BitVec.ofNat 32 tl6.header) (BitVec.ofNat 32 tl6.len).toNat) = .ok to15 ∧
    ∃ tl20, derElement 0x31 (memBytes M0 (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)).toNat) = .ok tl20 ∧
    (((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) = 0) ∧
    listsOidOf M0 p0 ((L0) - (rem)).toNat (memBytes M0 op15 ol15.toNat) = .ok false ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xF5C (reg n') ∧
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
        reg n' (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header ∧
        reg n' (26 : Fin 32) = ol15 ∧
        reg n' (27 : Fin 32) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len ∧
        SvKeepL B n0.mem n'.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xEA0: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_ea0 (off' := 0xEA4) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x260 = B + 0x21A0 + BitVec.ofNat 32 0x260 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0xEA4 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
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
  have g1_24 : reg n1 (24 : Fin 32) = rem := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = L0 := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x260 = B + 0x21A0 + BitVec.ofNat 32 0x260 by sv_addr, w0_260]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m1]; exact w0_64
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m1]; exact w0_7c
  have w1_25c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m1]; exact w0_25c
  have w1_260 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m1]; exact w0_260
  have w1_264 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m1]; exact w0_264
  have w1_268 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m1]; exact w0_268
  by_cases hle : (rem).toNat ≤ (L0).toNat
  rotate_left
  · -- 0xEA4: branch, taken
    obtain ⟨n2, d2, u2⟩ := s1.taken E1.self 0x107C sv_at_ea4
      (by decide) (by rw [g1_27, g1_24]; exact br_bltu_t (by omega))
    have s2 : St n2.mem SV n2 0x107C (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
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
    have g2_27 : reg n2 (27 : Fin 32) = L0 := by rw [u2.regs, g1_27]
    have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
    clear keep_kk1
    have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m2]; exact w1_64
    have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m2]; exact w1_7c
    have w2_25c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m2]; exact w1_25c
    have w2_260 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m2]; exact w1_260
    have w2_264 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m2]; exact w1_264
    have w2_268 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m2]; exact w1_268
    clear w1_268 w1_264 w1_260 w1_25c w1_7c w1_64 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
    -- 0x107C
    obtain ⟨n3, c3, u3⟩ := s2.block svTra107c E2.self svTra107c_end
      ⟨trivial, trivial⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have s3 : St n3.mem SV n3 0x107E (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have rb3 : ∀ q, reg n3 q = (runBlock svTra107c (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
    have g3_18 : reg n3 (18 : Fin 32) = out := by
      rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by
      rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = x20 := by
      rw [rb3, runBlock_reg _ _ _ (20 : Fin 32) s2.zero (by decide), g2_20]
    have g3_21 : reg n3 (21 : Fin 32) = x21 := by
      rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = x22 := by
      rw [rb3, runBlock_reg _ _ _ (22 : Fin 32) s2.zero (by decide), g2_22]
    have g3_23 : reg n3 (23 : Fin 32) = x23 := by
      rw [rb3, runBlock_reg _ _ _ (23 : Fin 32) s2.zero (by decide), g2_23]
    have g3_24 : reg n3 (24 : Fin 32) = rem := by
      rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
    have g3_25 : reg n3 (25 : Fin 32) = x25 := by
      rw [rb3, runBlock_reg _ _ _ (25 : Fin 32) s2.zero (by decide), g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = x26 := by
      rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = L0 := by
      rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
    have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x6 := by
      rw [rb3]; simp +decide only [runBlock, BInstr.run, svTra107c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m3]; exact w2_64
    have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m3]; exact w2_7c
    have w3_25c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m3]; exact w2_25c
    have w3_260 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m3]; exact w2_260
    have w3_264 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m3]; exact w2_264
    have w3_268 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m3]; exact w2_268
    clear w2_268 w2_264 w2_260 w2_25c w2_7c w2_64 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
    -- 0x107E: j
    obtain ⟨n4, d4, u4⟩ := s3.jump E3.self sv_at_107e (off' := 0x7A4) (by decide)
      (by rw [s3.pc]; decide)
    have s4 : St n4.mem SV n4 0x7A4 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
    have g4_8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 0x6 := by rw [u4.regs, g3_8]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, g3_20]
    have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, g3_22]
    have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, g3_23]
    have g4_24 : reg n4 (24 : Fin 32) = rem := by rw [u4.regs, g3_24]
    have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [u4.regs, g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = L0 := by rw [u4.regs, g3_27]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m4]; exact w3_64
    have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m4]; exact w3_7c
    have w4_25c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m4]; exact w3_25c
    have w4_260 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m4]; exact w3_260
    have w4_264 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m4]; exact w3_264
    have w4_268 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m4]; exact w3_268
    clear w3_268 w3_264 w3_260 w3_25c w3_7c w3_64 g3_8 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hle h0'), sv_fail F E4 s4 t4 (fun x hx => (fR4 x hx).trans (fM x hx).symm) V4 hret g4_2 g4_18 hO g4_3 g4_4⟩
  -- 0xEA4: branch, not taken
  obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.self 0xEA8 sv_at_ea4
    (by decide) (by rw [g1_27, g1_24]; exact br_bltu_f (by omega))
  have s2 : St n2.mem SV n2 0xEA8 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
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
  have g2_27 : reg n2 (27 : Fin 32) = L0 := by rw [u2.regs, g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m2]; exact w1_64
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m2]; exact w1_7c
  have w2_25c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m2]; exact w1_25c
  have w2_260 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m2]; exact w1_260
  have w2_264 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m2]; exact w1_264
  have w2_268 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m2]; exact w1_268
  clear w1_268 w1_264 w1_260 w1_25c w1_7c w1_64 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0xEA8: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_ea8 (off' := 0xEAC) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x25C = B + 0x21A0 + BitVec.ofNat 32 0x25C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0xEAC (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
  have g3_27 : reg n3 (27 : Fin 32) = L0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_10 : reg n3 a0 = p0 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x25C = B + 0x21A0 + BitVec.ofNat 32 0x25C by sv_addr, w2_25c]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m3]; exact w2_64
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m3]; exact w2_7c
  have w3_25c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m3]; exact w2_25c
  have w3_260 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m3]; exact w2_260
  have w3_264 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m3]; exact w2_264
  have w3_268 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m3]; exact w2_268
  clear w2_268 w2_264 w2_260 w2_25c w2_7c w2_64 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0xEAC: sw
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := sv_sw F E3 s3 sv_at_eac (off' := 0xEAE) (c := 0x40)
    (by decide) (by rw [g3_2]; sv_addr) (by decide) (by decide)
  have t4 : Steps n0 n4 := t3.trans d4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rg4 sp, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg4 (3 : Fin 32), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg4 (4 : Fin 32), g3_4]
  have g4_10 : reg n4 a0 = p0 := by rw [rg4 a0, g3_10]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rg4 (18 : Fin 32), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rg4 (19 : Fin 32), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [rg4 (20 : Fin 32), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [rg4 (21 : Fin 32), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [rg4 (22 : Fin 32), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [rg4 (23 : Fin 32), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = rem := by rw [rg4 (24 : Fin 32), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [rg4 (25 : Fin 32), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [rg4 (26 : Fin 32), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = L0 := by rw [rg4 (27 : Fin 32), g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x40, 0x4)] := keep_kk3.trans K4.toL
  clear keep_kk3
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K4.w32 (by decide) (by decide)).trans w3_64
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K4.w32 (by decide) (by decide)).trans w3_7c
  have w4_25c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K4.w32 (by decide) (by decide)).trans w3_25c
  have w4_260 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K4.w32 (by decide) (by decide)).trans w3_260
  have w4_264 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K4.w32 (by decide) (by decide)).trans w3_264
  have w4_268 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K4.w32 (by decide) (by decide)).trans w3_268
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [W4, g3_10]
  clear w3_268 w3_264 w3_260 w3_25c w3_7c w3_64 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0xEAE
  obtain ⟨n5, c5, u5⟩ := s4.block svTraeae E4.self svTraeae_end
    ⟨trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0xEB4 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svTraeae (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by
    rw [rb5, runBlock_reg _ _ _ sp s4.zero (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (3 : Fin 32) s4.zero (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (4 : Fin 32) s4.zero (by decide), g4_4]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = rem := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = L0 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svTraeae, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_10, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_11 : reg n5 a1 = B + 0x21A0 + BitVec.ofNat 32 0x25C := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svTraeae, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_10, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x40, 0x4)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m5]; exact w4_40
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m5]; exact w4_64
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m5]; exact w4_7c
  have w5_25c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m5]; exact w4_25c
  have w5_260 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m5]; exact w4_260
  have w5_264 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m5]; exact w4_264
  have w5_268 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m5]; exact w4_268
  clear w4_40 w4_268 w4_264 w4_260 w4_25c w4_7c w4_64 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 rg4 W4 K4 fr4 s4 d4
  -- 0xEB4: sv_seqF
  obtain ⟨n6, c6, s6, sp6, rk6, K6, Ok6, Er6, fr6⟩ := sv_seqF (oc := 0x420) (dc := 0x25C)
    F E5 s5 sv_at_eb4 sv_at_eb8 (by decide) (by decide) g5_2 g5_10 g5_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w5_264 w5_268 cr_in
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keepL K6 (by decide)
  rw [sv_mb fR5 cr_in] at Ok6 Er6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rk6 sp (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk6 (3 : Fin 32) (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk6 (4 : Fin 32) (by decide) (by decide), g5_4]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [rk6 (18 : Fin 32) (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [rk6 (19 : Fin 32) (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [rk6 (20 : Fin 32) (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [rk6 (21 : Fin 32) (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [rk6 (22 : Fin 32) (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [rk6 (23 : Fin 32) (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = rem := by rw [rk6 (24 : Fin 32) (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [rk6 (25 : Fin 32) (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [rk6 (26 : Fin 32) (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = L0 := by rw [rk6 (27 : Fin 32) (by decide) (by decide), g5_27]
  obtain ⟨r6, hr6⟩ : ∃ r, derElement 0x30 (memBytes M0 (cp) (rem).toNat) = r := ⟨_, rfl⟩
  rcases r6 with er6 | tl6
  · obtain ⟨z6, -⟩ := Er6 er6 hr6
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8)] := keep_kk5.trans K6
    clear keep_kk5
    have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K6.w32 (by decide) (by decide)).trans w5_40
    have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K6.w32 (by decide) (by decide)).trans w5_64
    have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K6.w32 (by decide) (by decide)).trans w5_7c
    have w6_25c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K6.w32 (by decide) (by decide)).trans w5_25c
    have w6_260 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K6.w32 (by decide) (by decide)).trans w5_260
    have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z6
    clear w5_268 w5_264 w5_260 w5_25c w5_7c w5_64 w5_40 g5_11 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
    -- 0xEBC: lw
    obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_ebc (off' := 0xEC0) (by decide)
      (by rw [g6_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s7 : St n7.mem SV n7 0xEC0 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = rem := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = L0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
    have g7_9 : reg n7 (9 : Fin 32) = 0 := by
      rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g6_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w6_420]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m7]; exact w6_40
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m7]; exact w6_64
    have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m7]; exact w6_7c
    have w7_25c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m7]; exact w6_25c
    have w7_260 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m7]; exact w6_260
    have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m7]; exact w6_420
    clear w6_420 w6_260 w6_25c w6_7c w6_64 w6_40 z6
    -- 0xEC0: lbu
    obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_ec0 (off' := 0xEC4) (by decide)
    have s8 : St n8.mem SV n8 0xEC4 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
    have g8_9 : reg n8 (9 : Fin 32) = 0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = rem := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = L0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m8]; exact w7_40
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m8]; exact w7_64
    have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m8]; exact w7_7c
    have w8_25c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m8]; exact w7_25c
    have w8_260 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m8]; exact w7_260
    have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m8]; exact w7_420
    clear w7_420 w7_260 w7_25c w7_7c w7_64 w7_40 g7_9 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
    -- 0xEC4: branch, taken
    obtain ⟨n9, d9, u9⟩ := s8.taken E8.self 0x7A4 sv_at_ec4
      (by decide) (by rw [g8_9, s8.zero]; rfl)
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
    have g9_9 : reg n9 (9 : Fin 32) = 0 := by rw [u9.regs, g8_9]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = rem := by rw [u9.regs, g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = L0 := by rw [u9.regs, g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m9]; exact w8_40
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m9]; exact w8_64
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m9]; exact w8_7c
    have w9_25c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m9]; exact w8_25c
    have w9_260 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m9]; exact w8_260
    have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m9]; exact w8_420
    clear w8_420 w8_260 w8_25c w8_7c w8_64 w8_40 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    exact .inl ⟨(fun ⟨h0', tl6', h1', _⟩ => by rw [hr6] at h1'; cases h1'), sv_fail F E9 s9 t9 (fun x hx => (fR9 x hx).trans (fM x hx).symm) V9 hret g9_2 g9_18 hO g9_3 g9_4⟩
  obtain ⟨o0_6, o4_6, o8_6, o12_6, d8_6, d12_6⟩ := Ok6 tl6 hr6
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8)] := keep_kk5.trans K6
  clear keep_kk5
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K6.w32 (by decide) (by decide)).trans w5_40
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K6.w32 (by decide) (by decide)).trans w5_64
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K6.w32 (by decide) (by decide)).trans w5_7c
  have w6_25c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K6.w32 (by decide) (by decide)).trans w5_25c
  have w6_260 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K6.w32 (by decide) (by decide)).trans w5_260
  have w6_264 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := d8_6
  have w6_268 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := d12_6
  have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cp) + BitVec.ofNat 32 tl6.header := o0_6
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl6.len := o4_6
  have w6_428 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := o8_6
  have w6_42c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := o12_6
  clear w5_268 w5_264 w5_260 w5_25c w5_7c w5_64 w5_40 g5_11 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0xEBC: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_ebc (off' := 0xEC0) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0xEC0 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = rem := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = L0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
  have g7_9 : reg n7 (9 : Fin 32) = (cp) + BitVec.ofNat 32 tl6.header := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w6_420]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m7]; exact w6_40
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m7]; exact w6_64
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m7]; exact w6_7c
  have w7_25c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m7]; exact w6_25c
  have w7_260 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m7]; exact w6_260
  have w7_264 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m7]; exact w6_264
  have w7_268 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m7]; exact w6_268
  have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m7]; exact w6_420
  have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl6.len := by rw [m7]; exact w6_424
  have w7_428 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m7]; exact w6_428
  have w7_42c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m7]; exact w6_42c
  clear w6_42c w6_428 w6_424 w6_420 w6_268 w6_264 w6_260 w6_25c w6_7c w6_64 w6_40 d12_6 d8_6 o12_6 o8_6 o4_6 o0_6 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 Er6 Ok6 K6 rk6 sp6 s6 c6
  -- 0xEC0: lbu
  obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_ec0 (off' := 0xEC4) (by decide)
  have b7_424 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by
    have h := byte_of_ld w7_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s8 : St n8.mem SV n8 0xEC4 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
  have g8_9 : reg n8 (9 : Fin 32) = (cp) + BitVec.ofNat 32 tl6.header := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = rem := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = L0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
  have g8_8 : reg n8 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b7_424]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m8]; exact w7_40
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m8]; exact w7_64
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m8]; exact w7_7c
  have w8_25c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m8]; exact w7_25c
  have w8_260 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m8]; exact w7_260
  have w8_264 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m8]; exact w7_264
  have w8_268 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m8]; exact w7_268
  have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m8]; exact w7_420
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl6.len := by rw [m8]; exact w7_424
  have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m8]; exact w7_428
  have w8_42c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m8]; exact w7_42c
  have b8_424 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m8]; exact b7_424
  clear w7_42c w7_428 w7_424 w7_420 w7_268 w7_264 w7_260 w7_25c w7_7c w7_64 w7_40 g7_9 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0xEC4: branch, not taken
  obtain ⟨n9, d9, u9⟩ := s8.notTaken E8.self 0xEC8 sv_at_ec4
    (by decide) (by rw [g8_9, s8.zero]; exact br_beq_f (cr_in.ok_ne hr6))
  have s9 : St n9.mem SV n9 0xEC8 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [u9.regs, g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = (cp) + BitVec.ofNat 32 tl6.header := by rw [u9.regs, g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = rem := by rw [u9.regs, g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = L0 := by rw [u9.regs, g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m9]; exact w8_40
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m9]; exact w8_64
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m9]; exact w8_7c
  have w9_25c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m9]; exact w8_25c
  have w9_260 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m9]; exact w8_260
  have w9_264 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m9]; exact w8_264
  have w9_268 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m9]; exact w8_268
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m9]; exact w8_420
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl6.len := by rw [m9]; exact w8_424
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m9]; exact w8_428
  have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m9]; exact w8_42c
  have b9_424 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m9]; exact b8_424
  clear b8_424 w8_42c w8_428 w8_424 w8_420 w8_268 w8_264 w8_260 w8_25c w8_7c w8_64 w8_40 g8_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 b7_424 u8 d8
  -- 0xEC8
  obtain ⟨n10, c10, u10⟩ := s9.block svTraec8 E9.self svTraec8_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0xED2 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svTraec8 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_8 : reg n10 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = (cp) + BitVec.ofNat 32 tl6.header := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by
    rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = rem := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = L0 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x3E5 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svTraec8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_11 : reg n10 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svTraec8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_12 : reg n10 a2 = BitVec.ofNat 32 0xB := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svTraec8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m10]; exact w9_40
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m10]; exact w9_64
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m10]; exact w9_7c
  have w10_25c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m10]; exact w9_25c
  have w10_260 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m10]; exact w9_260
  have w10_264 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m10]; exact w9_264
  have w10_268 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m10]; exact w9_268
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m10]; exact w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl6.len := by rw [m10]; exact w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m10]; exact w9_428
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m10]; exact w9_42c
  have b10_424 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m10]; exact b9_424
  clear b9_424 w9_42c w9_428 w9_424 w9_420 w9_268 w9_264 w9_260 w9_25c w9_7c w9_64 w9_40 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  have b10_425 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by
    have h := byte_of_ld w10_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b10_426 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by
    have h := byte_of_ld w10_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b10_427 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by
    have h := byte_of_ld w10_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0xED2: memcpy
  obtain ⟨n11, P11, K11, X11⟩ := sv_mc (c := 0x3E5) (d := 0x425) (N := 0xB) F E10 s10 sv_at_ed2 sv_at_ed6
    (by decide) (by decide) g10_2 g10_10 g10_11 g10_12
    (by decide) (by decide) (by decide)
  have s11 := P11.st
  have fr11 := P11.fr
  have t11 : Steps n0 n11 := t10.trans P11.steps
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [P11.regs sp (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P11.regs (3 : Fin 32) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P11.regs (4 : Fin 32) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [P11.regs (8 : Fin 32) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = (cp) + BitVec.ofNat 32 tl6.header := by rw [P11.regs (9 : Fin 32) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [P11.regs (18 : Fin 32) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [P11.regs (19 : Fin 32) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [P11.regs (20 : Fin 32) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [P11.regs (21 : Fin 32) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [P11.regs (22 : Fin 32) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [P11.regs (23 : Fin 32) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = rem := by rw [P11.regs (24 : Fin 32) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [P11.regs (25 : Fin 32) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [P11.regs (26 : Fin 32) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = L0 := by rw [P11.regs (27 : Fin 32) (by decide), g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K11.w32 (by decide) (by decide)).trans w10_40
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K11.w32 (by decide) (by decide)).trans w10_64
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K11.w32 (by decide) (by decide)).trans w10_7c
  have w11_25c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K11.w32 (by decide) (by decide)).trans w10_25c
  have w11_260 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K11.w32 (by decide) (by decide)).trans w10_260
  have w11_264 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K11.w32 (by decide) (by decide)).trans w10_264
  have w11_268 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K11.w32 (by decide) (by decide)).trans w10_268
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cp) + BitVec.ofNat 32 tl6.header := (K11.w32 (by decide) (by decide)).trans w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl6.len := (K11.w32 (by decide) (by decide)).trans w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := (K11.w32 (by decide) (by decide)).trans w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := (K11.w32 (by decide) (by decide)).trans w10_42c
  have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_424
  have b11_425 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K11.b8 (by decide) (by decide)).trans b10_425
  have b11_426 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K11.b8 (by decide) (by decide)).trans b10_426
  have b11_427 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K11.b8 (by decide) (by decide)).trans b10_427
  have w11_3e8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (cp) + BitVec.ofNat 32 tl6.header := by
    rw [← w10_428]
    exact ld_cp fun q hq => by
      have := X11 (0x3 + q) (by omega)
      rwa [show 0x3E5 + (0x3 + q) = 0x3E8 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w11_3ec : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl6.len := by
    rw [← w10_42c]
    exact ld_cp fun q hq => by
      have := X11 (0x7 + q) (by omega)
      rwa [show 0x3E5 + (0x7 + q) = 0x3EC + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b11_3e5 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [show 0x3E5 = 0x3E5 + 0x0 from rfl, X11 0x0 (by decide)]; exact b10_425
  have b11_3e6 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [show 0x3E6 = 0x3E5 + 0x1 from rfl, X11 0x1 (by decide)]; exact b10_426
  have b11_3e7 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [show 0x3E7 = 0x3E5 + 0x2 from rfl, X11 0x2 (by decide)]; exact b10_427
  clear b10_424 w10_42c w10_428 w10_424 w10_420 w10_268 w10_264 w10_260 w10_25c w10_7c w10_64 w10_40 g10_12 g10_11 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0xEDA: sw
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sw F E11 s11 sv_at_eda (off' := 0xEDE) (c := 0x3E0)
    (by decide) (by rw [g11_2]; sv_addr) (by decide) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg12 (8 : Fin 32), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = (cp) + BitVec.ofNat 32 tl6.header := by rw [rg12 (9 : Fin 32), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [rg12 (20 : Fin 32), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [rg12 (21 : Fin 32), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [rg12 (22 : Fin 32), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [rg12 (23 : Fin 32), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = rem := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [rg12 (25 : Fin 32), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = L0 := by rw [rg12 (27 : Fin 32), g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K12.w32 (by decide) (by decide)).trans w11_40
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K12.w32 (by decide) (by decide)).trans w11_64
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K12.w32 (by decide) (by decide)).trans w11_7c
  have w12_25c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K12.w32 (by decide) (by decide)).trans w11_25c
  have w12_260 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K12.w32 (by decide) (by decide)).trans w11_260
  have w12_264 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K12.w32 (by decide) (by decide)).trans w11_264
  have w12_268 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K12.w32 (by decide) (by decide)).trans w11_268
  have w12_3e8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (cp) + BitVec.ofNat 32 tl6.header := (K12.w32 (by decide) (by decide)).trans w11_3e8
  have w12_3ec : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl6.len := (K12.w32 (by decide) (by decide)).trans w11_3ec
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cp) + BitVec.ofNat 32 tl6.header := (K12.w32 (by decide) (by decide)).trans w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl6.len := (K12.w32 (by decide) (by decide)).trans w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := (K12.w32 (by decide) (by decide)).trans w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := (K12.w32 (by decide) (by decide)).trans w11_42c
  have b12_3e5 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K12.b8 (by decide) (by decide)).trans b11_3e5
  have b12_3e6 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K12.b8 (by decide) (by decide)).trans b11_3e6
  have b12_3e7 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K12.b8 (by decide) (by decide)).trans b11_3e7
  have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K12.b8 (by decide) (by decide)).trans b11_424
  have b12_425 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K12.b8 (by decide) (by decide)).trans b11_425
  have b12_426 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K12.b8 (by decide) (by decide)).trans b11_426
  have b12_427 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K12.b8 (by decide) (by decide)).trans b11_427
  have w12_3e0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [W12, g11_9]
  clear b11_3e7 b11_3e6 b11_3e5 w11_3ec w11_3e8 b11_427 b11_426 b11_425 b11_424 w11_42c w11_428 w11_424 w11_420 w11_268 w11_264 w11_260 w11_25c w11_7c w11_64 w11_40 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 s11 X11 K11 P11 b10_427 b10_426 b10_425
  -- 0xEDE: sb
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := sv_sb F E12 s12 sv_at_ede (off' := 0xEE2) (c := 0x3E4)
    (by decide) (by rw [g12_2]; sv_addr) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg13 (8 : Fin 32), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = (cp) + BitVec.ofNat 32 tl6.header := by rw [rg13 (9 : Fin 32), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rg13 (18 : Fin 32), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rg13 (19 : Fin 32), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [rg13 (20 : Fin 32), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [rg13 (21 : Fin 32), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [rg13 (22 : Fin 32), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [rg13 (23 : Fin 32), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = rem := by rw [rg13 (24 : Fin 32), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [rg13 (25 : Fin 32), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [rg13 (26 : Fin 32), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = L0 := by rw [rg13 (27 : Fin 32), g12_27]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K13.w32 (by decide) (by decide)).trans w12_40
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K13.w32 (by decide) (by decide)).trans w12_64
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K13.w32 (by decide) (by decide)).trans w12_7c
  have w13_25c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K13.w32 (by decide) (by decide)).trans w12_25c
  have w13_260 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K13.w32 (by decide) (by decide)).trans w12_260
  have w13_264 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K13.w32 (by decide) (by decide)).trans w12_264
  have w13_268 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K13.w32 (by decide) (by decide)).trans w12_268
  have w13_3e0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := (K13.w32 (by decide) (by decide)).trans w12_3e0
  have w13_3e8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (cp) + BitVec.ofNat 32 tl6.header := (K13.w32 (by decide) (by decide)).trans w12_3e8
  have w13_3ec : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl6.len := (K13.w32 (by decide) (by decide)).trans w12_3ec
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cp) + BitVec.ofNat 32 tl6.header := (K13.w32 (by decide) (by decide)).trans w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl6.len := (K13.w32 (by decide) (by decide)).trans w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := (K13.w32 (by decide) (by decide)).trans w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := (K13.w32 (by decide) (by decide)).trans w12_42c
  have b13_3e5 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K13.b8 (by decide) (by decide)).trans b12_3e5
  have b13_3e6 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K13.b8 (by decide) (by decide)).trans b12_3e6
  have b13_3e7 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K13.b8 (by decide) (by decide)).trans b12_3e7
  have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K13.b8 (by decide) (by decide)).trans b12_424
  have b13_425 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K13.b8 (by decide) (by decide)).trans b12_425
  have b13_426 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K13.b8 (by decide) (by decide)).trans b12_426
  have b13_427 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K13.b8 (by decide) (by decide)).trans b12_427
  have b13_3e4 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [W13, g12_8, lbu_low]
  clear w12_3e0 b12_427 b12_426 b12_425 b12_424 b12_3e7 b12_3e6 b12_3e5 w12_42c w12_428 w12_424 w12_420 w12_3ec w12_3e8 w12_268 w12_264 w12_260 w12_25c w12_7c w12_64 w12_40 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  have w13_3e4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := ld_of_bytes b13_3e4
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x3E4 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x3E5 by sv_addr]; exact b13_3e5)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x3E4 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x3E6 by sv_addr]; exact b13_3e6)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x3E4 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x3E7 by sv_addr]; exact b13_3e7)
  -- 0xEE2
  obtain ⟨n14, c14, u14⟩ := s13.block svTraee2 E13.self svTraee2_end
    ⟨trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem SV n14 0xEE8 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock svTraee2 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_8 : reg n14 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = (cp) + BitVec.ofNat 32 tl6.header := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
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
  have g14_27 : reg n14 (27 : Fin 32) = L0 := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTraee2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g14_11 : reg n14 a1 = B + 0x21A0 + BitVec.ofNat 32 0x3E0 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTraee2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m14]; exact w13_40
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m14]; exact w13_64
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m14]; exact w13_7c
  have w14_25c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m14]; exact w13_25c
  have w14_260 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m14]; exact w13_260
  have w14_264 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m14]; exact w13_264
  have w14_268 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m14]; exact w13_268
  have w14_3e0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m14]; exact w13_3e0
  have w14_3e4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m14]; exact w13_3e4
  have w14_3e8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m14]; exact w13_3e8
  have w14_3ec : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl6.len := by rw [m14]; exact w13_3ec
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m14]; exact w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl6.len := by rw [m14]; exact w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m14]; exact w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m14]; exact w13_42c
  have b14_424 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m14]; exact b13_424
  have b14_425 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m14]; exact b13_425
  have b14_426 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m14]; exact b13_426
  have b14_427 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m14]; exact b13_427
  clear b13_3e4 b13_427 b13_426 b13_425 b13_424 b13_3e7 b13_3e6 b13_3e5 w13_42c w13_428 w13_424 w13_420 w13_3ec w13_3e8 w13_3e0 w13_268 w13_264 w13_260 w13_25c w13_7c w13_64 w13_40 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  -- 0xEE8: sv_oidF
  obtain ⟨n15, c15, s15, sp15, rk15, K15, A15, Ok15, Er15, fr15⟩ := sv_oidF (oc := 0x420) (dc := 0x3E0)
    F E14 s14 sv_at_ee8 sv_at_eec (by decide) (by decide) g14_2 g14_10 g14_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w14_3e8 w14_3ec (cr_in.contentW hr6)
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keepL K15 (by decide)
  rw [sv_mb fR14 (cr_in.contentW hr6)] at A15 Ok15 Er15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rk15 sp (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk15 (3 : Fin 32) (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk15 (4 : Fin 32) (by decide) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk15 (8 : Fin 32) (by decide) (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = (cp) + BitVec.ofNat 32 tl6.header := by rw [rk15 (9 : Fin 32) (by decide) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rk15 (18 : Fin 32) (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rk15 (19 : Fin 32) (by decide) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [rk15 (20 : Fin 32) (by decide) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [rk15 (21 : Fin 32) (by decide) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [rk15 (22 : Fin 32) (by decide) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [rk15 (23 : Fin 32) (by decide) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = rem := by rw [rk15 (24 : Fin 32) (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [rk15 (25 : Fin 32) (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [rk15 (26 : Fin 32) (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = L0 := by rw [rk15 (27 : Fin 32) (by decide) (by decide), g14_27]
  obtain ⟨r15, hr15⟩ : ∃ r, derContent ((cp) + BitVec.ofNat 32 tl6.header) (derOid (memBytes M0 ((cp) + BitVec.ofNat 32 tl6.header) (BitVec.ofNat 32 tl6.len).toNat)) = r := ⟨_, rfl⟩
  rcases r15 with er15 | ⟨op15, ol15⟩
  · obtain ⟨z15, -⟩ := Er15 er15 hr15
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8)] := keep_kk14.trans K15
    clear keep_kk14
    have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K15.w32 (by decide) (by decide)).trans w14_40
    have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K15.w32 (by decide) (by decide)).trans w14_64
    have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K15.w32 (by decide) (by decide)).trans w14_7c
    have w15_25c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K15.w32 (by decide) (by decide)).trans w14_25c
    have w15_260 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K15.w32 (by decide) (by decide)).trans w14_260
    have w15_264 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K15.w32 (by decide) (by decide)).trans w14_264
    have w15_268 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K15.w32 (by decide) (by decide)).trans w14_268
    have w15_3e0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := (K15.w32 (by decide) (by decide)).trans w14_3e0
    have w15_3e4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := (K15.w32 (by decide) (by decide)).trans w14_3e4
    have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := (K15.w32 (by decide) (by decide)).trans w14_428
    have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := (K15.w32 (by decide) (by decide)).trans w14_42c
    have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z15
    clear b14_427 b14_426 b14_425 b14_424 w14_42c w14_428 w14_424 w14_420 w14_3ec w14_3e8 w14_3e4 w14_3e0 w14_268 w14_264 w14_260 w14_25c w14_7c w14_64 w14_40 g14_11 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14 w13_3e4
    -- 0xEF0: lw
    obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_ef0 (off' := 0xEF4) (by decide)
      (by rw [g15_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s16 : St n16.mem SV n16 0xEF4 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
    have g16_8 : reg n16 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_8]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = rem := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = L0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
    have g16_9 : reg n16 (9 : Fin 32) = 0 := by
      rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g15_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w15_420]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m16]; exact w15_40
    have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m16]; exact w15_64
    have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m16]; exact w15_7c
    have w16_25c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m16]; exact w15_25c
    have w16_260 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m16]; exact w15_260
    have w16_264 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m16]; exact w15_264
    have w16_268 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m16]; exact w15_268
    have w16_3e0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m16]; exact w15_3e0
    have w16_3e4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m16]; exact w15_3e4
    have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m16]; exact w15_420
    have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m16]; exact w15_428
    have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m16]; exact w15_42c
    clear w15_420 w15_42c w15_428 w15_3e4 w15_3e0 w15_268 w15_264 w15_260 w15_25c w15_7c w15_64 w15_40 z15
    -- 0xEF4: branch, taken
    obtain ⟨n17, d17, u17⟩ := s16.taken E16.self 0x12AA sv_at_ef4
      (by decide) (by rw [g16_9, s16.zero]; rfl)
    have s17 : St n17.mem SV n17 0x12AA (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [u17.regs, g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = 0 := by rw [u17.regs, g16_9]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = rem := by rw [u17.regs, g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = L0 := by rw [u17.regs, g16_27]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m17]; exact w16_40
    have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m17]; exact w16_64
    have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m17]; exact w16_7c
    have w17_25c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m17]; exact w16_25c
    have w17_260 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m17]; exact w16_260
    have w17_264 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m17]; exact w16_264
    have w17_268 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m17]; exact w16_268
    have w17_3e0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m17]; exact w16_3e0
    have w17_3e4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m17]; exact w16_3e4
    have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m17]; exact w16_420
    have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m17]; exact w16_428
    have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m17]; exact w16_42c
    clear w16_42c w16_428 w16_420 w16_3e4 w16_3e0 w16_268 w16_264 w16_260 w16_25c w16_7c w16_64 w16_40 g16_9 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    -- 0x12AA: lbu
    obtain ⟨n18, d18, u18⟩ := s17.lbu E17.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s18 : St n18.mem SV n18 0x12AE (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
    have g18_9 : reg n18 (9 : Fin 32) = 0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_9]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
    have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_20]
    have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = rem := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = L0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m18]; exact keep_kk17
    clear keep_kk17
    have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m18]; exact w17_40
    have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m18]; exact w17_64
    have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m18]; exact w17_7c
    have w18_25c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m18]; exact w17_25c
    have w18_260 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m18]; exact w17_260
    have w18_264 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m18]; exact w17_264
    have w18_268 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m18]; exact w17_268
    have w18_3e0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m18]; exact w17_3e0
    have w18_3e4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m18]; exact w17_3e4
    have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m18]; exact w17_420
    have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m18]; exact w17_428
    have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m18]; exact w17_42c
    clear w17_42c w17_428 w17_420 w17_3e4 w17_3e0 w17_268 w17_264 w17_260 w17_25c w17_7c w17_64 w17_40 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
    -- 0x12AE: j
    obtain ⟨n19, d19, u19⟩ := s18.jump E18.self sv_at_12ae (off' := 0x7A4) (by decide)
      (by rw [s18.pc]; decide)
    have s19 : St n19.mem SV n19 0x7A4 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
    have g19_9 : reg n19 (9 : Fin 32) = 0 := by rw [u19.regs, g18_9]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = rem := by rw [u19.regs, g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = L0 := by rw [u19.regs, g18_27]
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m19]; exact w18_40
    have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m19]; exact w18_64
    have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m19]; exact w18_7c
    have w19_25c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m19]; exact w18_25c
    have w19_260 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m19]; exact w18_260
    have w19_264 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m19]; exact w18_264
    have w19_268 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m19]; exact w18_268
    have w19_3e0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m19]; exact w18_3e0
    have w19_3e4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m19]; exact w18_3e4
    have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m19]; exact w18_420
    have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m19]; exact w18_428
    have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m19]; exact w18_42c
    clear w18_42c w18_428 w18_420 w18_3e4 w18_3e0 w18_268 w18_264 w18_260 w18_25c w18_7c w18_64 w18_40 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    exact .inl ⟨(fun ⟨h0', tl6', h1', op15', ol15', h2', _⟩ => by rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'), sv_fail F E19 s19 t19 (fun x hx => (fR19 x hx).trans (fM x hx).symm) V19 hret g19_2 g19_18 hO g19_3 g19_4⟩
  obtain ⟨to15, ht15, -, -⟩ := oid_ok_content hr15
  obtain ⟨p0_15, p4_15⟩ := Ok15 op15 ol15 hr15
  obtain ⟨d8_15, d12_15⟩ := A15 to15 (derOid_ok_elem ht15)
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8)] := keep_kk14.trans K15
  clear keep_kk14
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K15.w32 (by decide) (by decide)).trans w14_40
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K15.w32 (by decide) (by decide)).trans w14_64
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K15.w32 (by decide) (by decide)).trans w14_7c
  have w15_25c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K15.w32 (by decide) (by decide)).trans w14_25c
  have w15_260 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K15.w32 (by decide) (by decide)).trans w14_260
  have w15_264 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K15.w32 (by decide) (by decide)).trans w14_264
  have w15_268 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K15.w32 (by decide) (by decide)).trans w14_268
  have w15_3e0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := (K15.w32 (by decide) (by decide)).trans w14_3e0
  have w15_3e4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := (K15.w32 (by decide) (by decide)).trans w14_3e4
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := (K15.w32 (by decide) (by decide)).trans w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := (K15.w32 (by decide) (by decide)).trans w14_42c
  have w15_3e8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len) := d8_15
  have w15_3ec : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = (BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len) := d12_15
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op15 := p0_15
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol15 := p4_15
  clear b14_427 b14_426 b14_425 b14_424 w14_42c w14_428 w14_424 w14_420 w14_3ec w14_3e8 w14_3e4 w14_3e0 w14_268 w14_264 w14_260 w14_25c w14_7c w14_64 w14_40 g14_11 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14 w13_3e4
  -- 0xEF0: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_ef0 (off' := 0xEF4) (by decide)
    (by rw [g15_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s16 : St n16.mem SV n16 0xEF4 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_8]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = rem := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = L0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
  have g16_9 : reg n16 (9 : Fin 32) = op15 := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w15_420]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m16]; exact w15_40
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m16]; exact w15_64
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m16]; exact w15_7c
  have w16_25c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m16]; exact w15_25c
  have w16_260 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m16]; exact w15_260
  have w16_264 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m16]; exact w15_264
  have w16_268 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m16]; exact w15_268
  have w16_3e0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m16]; exact w15_3e0
  have w16_3e4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m16]; exact w15_3e4
  have w16_3e8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len) := by rw [m16]; exact w15_3e8
  have w16_3ec : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = (BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len) := by rw [m16]; exact w15_3ec
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op15 := by rw [m16]; exact w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol15 := by rw [m16]; exact w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m16]; exact w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m16]; exact w15_42c
  clear w15_424 w15_420 w15_3ec w15_3e8 w15_42c w15_428 w15_3e4 w15_3e0 w15_268 w15_264 w15_260 w15_25c w15_7c w15_64 w15_40 d12_15 d8_15 p4_15 p0_15 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 Er15 Ok15 A15 K15 rk15 sp15 s15 c15
  -- 0xEF4: branch, not taken
  obtain ⟨n17, d17, u17⟩ := s16.notTaken E16.self 0xEF8 sv_at_ef4
    (by decide) (by rw [g16_9, s16.zero]; exact br_beq_f (((cr_in.contentW hr6).oidIn hr15).pos_ne))
  have s17 : St n17.mem SV n17 0xEF8 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [u17.regs, g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = op15 := by rw [u17.regs, g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = rem := by rw [u17.regs, g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = L0 := by rw [u17.regs, g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m17]; exact w16_40
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m17]; exact w16_64
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m17]; exact w16_7c
  have w17_25c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m17]; exact w16_25c
  have w17_260 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m17]; exact w16_260
  have w17_264 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m17]; exact w16_264
  have w17_268 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m17]; exact w16_268
  have w17_3e0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m17]; exact w16_3e0
  have w17_3e4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m17]; exact w16_3e4
  have w17_3e8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len) := by rw [m17]; exact w16_3e8
  have w17_3ec : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = (BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len) := by rw [m17]; exact w16_3ec
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op15 := by rw [m17]; exact w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol15 := by rw [m17]; exact w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m17]; exact w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m17]; exact w16_42c
  clear w16_42c w16_428 w16_424 w16_420 w16_3ec w16_3e8 w16_3e4 w16_3e0 w16_268 w16_264 w16_260 w16_25c w16_7c w16_64 w16_40 g16_9 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0xEF8: lw
  obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_ef8 (off' := 0xEFC) (by decide)
    (by rw [g17_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s18 : St n18.mem SV n18 0xEFC (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = op15 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = rem := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
  have g18_27 : reg n18 (27 : Fin 32) = L0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
  have g18_26 : reg n18 (26 : Fin 32) = ol15 := by
    rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g17_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w17_424]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m18]; exact w17_40
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m18]; exact w17_64
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m18]; exact w17_7c
  have w18_25c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m18]; exact w17_25c
  have w18_260 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m18]; exact w17_260
  have w18_264 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m18]; exact w17_264
  have w18_268 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m18]; exact w17_268
  have w18_3e0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m18]; exact w17_3e0
  have w18_3e4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m18]; exact w17_3e4
  have w18_3e8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len) := by rw [m18]; exact w17_3e8
  have w18_3ec : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = (BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len) := by rw [m18]; exact w17_3ec
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op15 := by rw [m18]; exact w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol15 := by rw [m18]; exact w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m18]; exact w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m18]; exact w17_42c
  clear w17_42c w17_428 w17_424 w17_420 w17_3ec w17_3e8 w17_3e4 w17_3e0 w17_268 w17_264 w17_260 w17_25c w17_7c w17_64 w17_40 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0xEFC
  obtain ⟨n19, c19, u19⟩ := s18.block svTraefc E18.self svTraefc_end
    ⟨trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0xF02 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svTraefc (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
  have g19_8 : reg n19 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = op15 := by
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
  have g19_26 : reg n19 (26 : Fin 32) = ol15 := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = L0 := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svTraefc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0x3E0 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svTraefc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m19]; exact w18_40
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m19]; exact w18_64
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m19]; exact w18_7c
  have w19_25c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m19]; exact w18_25c
  have w19_260 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m19]; exact w18_260
  have w19_264 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m19]; exact w18_264
  have w19_268 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m19]; exact w18_268
  have w19_3e0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m19]; exact w18_3e0
  have w19_3e4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m19]; exact w18_3e4
  have w19_3e8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len) := by rw [m19]; exact w18_3e8
  have w19_3ec : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = (BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len) := by rw [m19]; exact w18_3ec
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op15 := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol15 := by rw [m19]; exact w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m19]; exact w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m19]; exact w18_42c
  clear w18_42c w18_428 w18_424 w18_420 w18_3ec w18_3e8 w18_3e4 w18_3e0 w18_268 w18_264 w18_260 w18_25c w18_7c w18_64 w18_40 g18_26 g18_27 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0xF02: sv_setF
  obtain ⟨n20, c20, s20, sp20, rk20, K20, Ok20, Er20, fr20⟩ := sv_setF (oc := 0x420) (dc := 0x3E0)
    F E19 s19 sv_at_f02 sv_at_f06 (by decide) (by decide) g19_2 g19_10 g19_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w19_3e8 w19_3ec ((cr_in.contentW hr6).restW (derOid_ok_elem ht15))
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keepL K20 (by decide)
  rw [sv_mb fR19 ((cr_in.contentW hr6).restW (derOid_ok_elem ht15))] at Ok20 Er20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [rk20 sp (by decide) (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk20 (3 : Fin 32) (by decide) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk20 (4 : Fin 32) (by decide) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk20 (8 : Fin 32) (by decide) (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = op15 := by rw [rk20 (9 : Fin 32) (by decide) (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rk20 (18 : Fin 32) (by decide) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rk20 (19 : Fin 32) (by decide) (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [rk20 (20 : Fin 32) (by decide) (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [rk20 (21 : Fin 32) (by decide) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [rk20 (22 : Fin 32) (by decide) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [rk20 (23 : Fin 32) (by decide) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = rem := by rw [rk20 (24 : Fin 32) (by decide) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [rk20 (25 : Fin 32) (by decide) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = ol15 := by rw [rk20 (26 : Fin 32) (by decide) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = L0 := by rw [rk20 (27 : Fin 32) (by decide) (by decide), g19_27]
  obtain ⟨r20, hr20⟩ : ∃ r, derElement 0x31 (memBytes M0 (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)).toNat) = r := ⟨_, rfl⟩
  rcases r20 with er20 | tl20
  · obtain ⟨z20, -⟩ := Er20 er20 hr20
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8)] := keep_kk19.trans K20
    clear keep_kk19
    have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K20.w32 (by decide) (by decide)).trans w19_40
    have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K20.w32 (by decide) (by decide)).trans w19_64
    have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K20.w32 (by decide) (by decide)).trans w19_7c
    have w20_25c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K20.w32 (by decide) (by decide)).trans w19_25c
    have w20_260 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K20.w32 (by decide) (by decide)).trans w19_260
    have w20_264 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K20.w32 (by decide) (by decide)).trans w19_264
    have w20_268 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K20.w32 (by decide) (by decide)).trans w19_268
    have w20_3e0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := (K20.w32 (by decide) (by decide)).trans w19_3e0
    have w20_3e4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := (K20.w32 (by decide) (by decide)).trans w19_3e4
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z20
    clear w19_42c w19_428 w19_424 w19_420 w19_3ec w19_3e8 w19_3e4 w19_3e0 w19_268 w19_264 w19_260 w19_25c w19_7c w19_64 w19_40 g19_11 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
    -- 0xF0A: lw
    obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_f0a (off' := 0xF0E) (by decide)
      (by rw [g20_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s21 : St n21.mem SV n21 0xF0E (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
    have g21_8 : reg n21 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_8]
    have g21_9 : reg n21 (9 : Fin 32) = op15 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = rem := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
    have g21_26 : reg n21 (26 : Fin 32) = ol15 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = L0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
    have g21_25 : reg n21 (25 : Fin 32) = 0 := by
      rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g20_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w20_420]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m21]; exact w20_40
    have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m21]; exact w20_64
    have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m21]; exact w20_7c
    have w21_25c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m21]; exact w20_25c
    have w21_260 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m21]; exact w20_260
    have w21_264 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m21]; exact w20_264
    have w21_268 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m21]; exact w20_268
    have w21_3e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m21]; exact w20_3e0
    have w21_3e4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m21]; exact w20_3e4
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m21]; exact w20_420
    clear w20_420 w20_3e4 w20_3e0 w20_268 w20_264 w20_260 w20_25c w20_7c w20_64 w20_40 z20
    -- 0xF0E: lbu
    obtain ⟨n22, d22, u22⟩ := s21.lbu E21.self sv_at_f0e (off' := 0xF12) (by decide)
    have s22 : St n22.mem SV n22 0xF12 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
    have g22_9 : reg n22 (9 : Fin 32) = op15 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = rem := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = 0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = ol15 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = L0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m22]; exact w21_40
    have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m22]; exact w21_64
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m22]; exact w21_7c
    have w22_25c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m22]; exact w21_25c
    have w22_260 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m22]; exact w21_260
    have w22_264 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m22]; exact w21_264
    have w22_268 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m22]; exact w21_268
    have w22_3e0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m22]; exact w21_3e0
    have w22_3e4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m22]; exact w21_3e4
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m22]; exact w21_420
    clear w21_420 w21_3e4 w21_3e0 w21_268 w21_264 w21_260 w21_25c w21_7c w21_64 w21_40 g21_25 g21_27 g21_26 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
    -- 0xF12: branch, taken
    obtain ⟨n23, d23, u23⟩ := s22.taken E22.self 0x7A4 sv_at_f12
      (by decide) (by rw [g22_25, s22.zero]; rfl)
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
    have g23_9 : reg n23 (9 : Fin 32) = op15 := by rw [u23.regs, g22_9]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [u23.regs, g22_20]
    have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [u23.regs, g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [u23.regs, g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = rem := by rw [u23.regs, g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = 0 := by rw [u23.regs, g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = ol15 := by rw [u23.regs, g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = L0 := by rw [u23.regs, g22_27]
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m23]; exact w22_40
    have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m23]; exact w22_64
    have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m23]; exact w22_7c
    have w23_25c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m23]; exact w22_25c
    have w23_260 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m23]; exact w22_260
    have w23_264 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m23]; exact w22_264
    have w23_268 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m23]; exact w22_268
    have w23_3e0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m23]; exact w22_3e0
    have w23_3e4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m23]; exact w22_3e4
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m23]; exact w22_420
    clear w22_420 w22_3e4 w22_3e0 w22_268 w22_264 w22_260 w22_25c w22_7c w22_64 w22_40 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    exact .inl ⟨(fun ⟨h0', tl6', h1', op15', ol15', h2', to15', h3', tl20', h4', _⟩ => by rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'; rw [ht15] at h3'; cases h3'; rw [hr20] at h4'; cases h4'), sv_fail F E23 s23 t23 (fun x hx => (fR23 x hx).trans (fM x hx).symm) V23 hret g23_2 g23_18 hO g23_3 g23_4⟩
  obtain ⟨o0_20, o4_20, o8_20, o12_20, d8_20, d12_20⟩ := Ok20 tl20 hr20
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8)] := keep_kk19.trans K20
  clear keep_kk19
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K20.w32 (by decide) (by decide)).trans w19_40
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K20.w32 (by decide) (by decide)).trans w19_64
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K20.w32 (by decide) (by decide)).trans w19_7c
  have w20_25c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K20.w32 (by decide) (by decide)).trans w19_25c
  have w20_260 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K20.w32 (by decide) (by decide)).trans w19_260
  have w20_264 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K20.w32 (by decide) (by decide)).trans w19_264
  have w20_268 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K20.w32 (by decide) (by decide)).trans w19_268
  have w20_3e0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := (K20.w32 (by decide) (by decide)).trans w19_3e0
  have w20_3e4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := (K20.w32 (by decide) (by decide)).trans w19_3e4
  have w20_3e8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := d8_20
  have w20_3ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := d12_20
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := o0_20
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := o4_20
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := o8_20
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := o12_20
  clear w19_42c w19_428 w19_424 w19_420 w19_3ec w19_3e8 w19_3e4 w19_3e0 w19_268 w19_264 w19_260 w19_25c w19_7c w19_64 w19_40 g19_11 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0xF0A: lw
  obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_f0a (off' := 0xF0E) (by decide)
    (by rw [g20_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s21 : St n21.mem SV n21 0xF0E (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = op15 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = rem := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
  have g21_26 : reg n21 (26 : Fin 32) = ol15 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = L0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
  have g21_25 : reg n21 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by
    rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g20_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w20_420]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m21]; exact w20_40
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m21]; exact w20_64
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m21]; exact w20_7c
  have w21_25c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m21]; exact w20_25c
  have w21_260 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m21]; exact w20_260
  have w21_264 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m21]; exact w20_264
  have w21_268 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m21]; exact w20_268
  have w21_3e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m21]; exact w20_3e0
  have w21_3e4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m21]; exact w20_3e4
  have w21_3e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m21]; exact w20_3e8
  have w21_3ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m21]; exact w20_3ec
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m21]; exact w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m21]; exact w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m21]; exact w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m21]; exact w20_42c
  clear w20_42c w20_428 w20_424 w20_420 w20_3ec w20_3e8 w20_3e4 w20_3e0 w20_268 w20_264 w20_260 w20_25c w20_7c w20_64 w20_40 d12_20 d8_20 o12_20 o8_20 o4_20 o0_20 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 Er20 Ok20 K20 rk20 sp20 s20 c20
  -- 0xF0E: lbu
  obtain ⟨n22, d22, u22⟩ := s21.lbu E21.self sv_at_f0e (off' := 0xF12) (by decide)
  have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by
    have h := byte_of_ld w21_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s22 : St n22.mem SV n22 0xF12 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
  have g22_9 : reg n22 (9 : Fin 32) = op15 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = rem := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = ol15 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = L0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
  have g22_8 : reg n22 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g21_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b21_424]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m22]; exact w21_40
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m22]; exact w21_64
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m22]; exact w21_7c
  have w22_25c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m22]; exact w21_25c
  have w22_260 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m22]; exact w21_260
  have w22_264 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m22]; exact w21_264
  have w22_268 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m22]; exact w21_268
  have w22_3e0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m22]; exact w21_3e0
  have w22_3e4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m22]; exact w21_3e4
  have w22_3e8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m22]; exact w21_3e8
  have w22_3ec : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m22]; exact w21_3ec
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m22]; exact w21_42c
  have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m22]; exact b21_424
  clear w21_42c w21_428 w21_424 w21_420 w21_3ec w21_3e8 w21_3e4 w21_3e0 w21_268 w21_264 w21_260 w21_25c w21_7c w21_64 w21_40 g21_25 g21_27 g21_26 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0xF12: branch, not taken
  obtain ⟨n23, d23, u23⟩ := s22.notTaken E22.self 0xF16 sv_at_f12
    (by decide) (by rw [g22_25, s22.zero]; exact br_beq_f (((cr_in.contentW hr6).restW (derOid_ok_elem ht15)).ok_ne hr20))
  have s23 : St n23.mem SV n23 0xF16 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by rw [u23.regs, g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = op15 := by rw [u23.regs, g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [u23.regs, g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [u23.regs, g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [u23.regs, g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = rem := by rw [u23.regs, g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u23.regs, g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = ol15 := by rw [u23.regs, g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = L0 := by rw [u23.regs, g22_27]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m23]; exact w22_40
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m23]; exact w22_64
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m23]; exact w22_7c
  have w23_25c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m23]; exact w22_25c
  have w23_260 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m23]; exact w22_260
  have w23_264 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m23]; exact w22_264
  have w23_268 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m23]; exact w22_268
  have w23_3e0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m23]; exact w22_3e0
  have w23_3e4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m23]; exact w22_3e4
  have w23_3e8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m23]; exact w22_3e8
  have w23_3ec : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m23]; exact w22_3ec
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m23]; exact w22_42c
  have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m23]; exact b22_424
  clear b22_424 w22_42c w22_428 w22_424 w22_420 w22_3ec w22_3e8 w22_3e4 w22_3e0 w22_268 w22_264 w22_260 w22_25c w22_7c w22_64 w22_40 g22_8 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 b21_424 u22 d22
  -- 0xF16
  obtain ⟨n24, c24, u24⟩ := s23.block svTraf16 E23.self svTraf16_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem SV n24 0xF20 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock svTraf16 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
  have g24_8 : reg n24 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = op15 := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
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
  have g24_25 : reg n24 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by
    rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = ol15 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = L0 := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_10 : reg n24 a0 = B + 0x21A0 + BitVec.ofNat 32 0x405 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svTraf16, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g24_11 : reg n24 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svTraf16, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g24_12 : reg n24 a2 = BitVec.ofNat 32 0xB := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svTraf16, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m24]; exact w23_40
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m24]; exact w23_64
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m24]; exact w23_7c
  have w24_25c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m24]; exact w23_25c
  have w24_260 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m24]; exact w23_260
  have w24_264 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m24]; exact w23_264
  have w24_268 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m24]; exact w23_268
  have w24_3e0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m24]; exact w23_3e0
  have w24_3e4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m24]; exact w23_3e4
  have w24_3e8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m24]; exact w23_3e8
  have w24_3ec : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m24]; exact w23_3ec
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m24]; exact w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m24]; exact w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m24]; exact w23_42c
  have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m24]; exact b23_424
  clear b23_424 w23_42c w23_428 w23_424 w23_420 w23_3ec w23_3e8 w23_3e4 w23_3e0 w23_268 w23_264 w23_260 w23_25c w23_7c w23_64 w23_40 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  have b24_425 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by
    have h := byte_of_ld w24_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b24_426 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by
    have h := byte_of_ld w24_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b24_427 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by
    have h := byte_of_ld w24_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0xF20: memcpy
  obtain ⟨n25, P25, K25, X25⟩ := sv_mc (c := 0x405) (d := 0x425) (N := 0xB) F E24 s24 sv_at_f20 sv_at_f24
    (by decide) (by decide) g24_2 g24_10 g24_11 g24_12
    (by decide) (by decide) (by decide)
  have s25 := P25.st
  have fr25 := P25.fr
  have t25 : Steps n0 n25 := t24.trans P25.steps
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [P25.regs sp (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P25.regs (3 : Fin 32) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P25.regs (4 : Fin 32) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by rw [P25.regs (8 : Fin 32) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = op15 := by rw [P25.regs (9 : Fin 32) (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [P25.regs (18 : Fin 32) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [P25.regs (19 : Fin 32) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [P25.regs (20 : Fin 32) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [P25.regs (21 : Fin 32) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [P25.regs (22 : Fin 32) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [P25.regs (23 : Fin 32) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = rem := by rw [P25.regs (24 : Fin 32) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [P25.regs (25 : Fin 32) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = ol15 := by rw [P25.regs (26 : Fin 32) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = L0 := by rw [P25.regs (27 : Fin 32) (by decide), g24_27]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB)] := keep_kk24.trans K25.toL
  clear keep_kk24
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K25.w32 (by decide) (by decide)).trans w24_40
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K25.w32 (by decide) (by decide)).trans w24_64
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K25.w32 (by decide) (by decide)).trans w24_7c
  have w25_25c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K25.w32 (by decide) (by decide)).trans w24_25c
  have w25_260 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K25.w32 (by decide) (by decide)).trans w24_260
  have w25_264 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K25.w32 (by decide) (by decide)).trans w24_264
  have w25_268 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K25.w32 (by decide) (by decide)).trans w24_268
  have w25_3e0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := (K25.w32 (by decide) (by decide)).trans w24_3e0
  have w25_3e4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := (K25.w32 (by decide) (by decide)).trans w24_3e4
  have w25_3e8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := (K25.w32 (by decide) (by decide)).trans w24_3e8
  have w25_3ec : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := (K25.w32 (by decide) (by decide)).trans w24_3ec
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K25.w32 (by decide) (by decide)).trans w24_420
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := (K25.w32 (by decide) (by decide)).trans w24_424
  have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K25.w32 (by decide) (by decide)).trans w24_428
  have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := (K25.w32 (by decide) (by decide)).trans w24_42c
  have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_424
  have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := (K25.b8 (by decide) (by decide)).trans b24_425
  have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := (K25.b8 (by decide) (by decide)).trans b24_426
  have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := (K25.b8 (by decide) (by decide)).trans b24_427
  have w25_408 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by
    rw [← w24_428]
    exact ld_cp fun q hq => by
      have := X25 (0x3 + q) (by omega)
      rwa [show 0x405 + (0x3 + q) = 0x408 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w25_40c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by
    rw [← w24_42c]
    exact ld_cp fun q hq => by
      have := X25 (0x7 + q) (by omega)
      rwa [show 0x405 + (0x7 + q) = 0x40C + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b25_405 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [show 0x405 = 0x405 + 0x0 from rfl, X25 0x0 (by decide)]; exact b24_425
  have b25_406 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [show 0x406 = 0x405 + 0x1 from rfl, X25 0x1 (by decide)]; exact b24_426
  have b25_407 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [show 0x407 = 0x405 + 0x2 from rfl, X25 0x2 (by decide)]; exact b24_427
  clear b24_424 w24_42c w24_428 w24_424 w24_420 w24_3ec w24_3e8 w24_3e4 w24_3e0 w24_268 w24_264 w24_260 w24_25c w24_7c w24_64 w24_40 g24_12 g24_11 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0xF28: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_f28 (off' := 0xF2C) (by decide)
    (by rw [g25_2, show B + 0x21A0 + 0x3EC = B + 0x21A0 + BitVec.ofNat 32 0x3EC by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0xF2C (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = op15 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = rem := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = ol15 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = L0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_10 : reg n26 a0 = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_2, show B + 0x21A0 + 0x3EC = B + 0x21A0 + BitVec.ofNat 32 0x3EC by sv_addr, w25_3ec]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m26]; exact w25_40
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m26]; exact w25_64
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m26]; exact w25_7c
  have w26_25c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m26]; exact w25_25c
  have w26_260 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m26]; exact w25_260
  have w26_264 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m26]; exact w25_264
  have w26_268 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m26]; exact w25_268
  have w26_3e0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m26]; exact w25_3e0
  have w26_3e4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m26]; exact w25_3e4
  have w26_3e8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m26]; exact w25_3e8
  have w26_3ec : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m26]; exact w25_3ec
  have w26_408 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m26]; exact w25_408
  have w26_40c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m26]; exact w25_40c
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m26]; exact w25_420
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m26]; exact w25_424
  have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m26]; exact w25_428
  have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m26]; exact w25_42c
  have b26_405 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m26]; exact b25_405
  have b26_406 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m26]; exact b25_406
  have b26_407 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m26]; exact b25_407
  have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m26]; exact b25_424
  have b26_425 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m26]; exact b25_425
  have b26_426 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m26]; exact b25_426
  have b26_427 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m26]; exact b25_427
  clear b25_407 b25_406 b25_405 w25_40c w25_408 b25_427 b25_426 b25_425 b25_424 w25_42c w25_428 w25_424 w25_420 w25_3ec w25_3e8 w25_3e4 w25_3e0 w25_268 w25_264 w25_260 w25_25c w25_7c w25_64 w25_40 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 s25 X25 K25 P25 b24_427 b24_426 b24_425
  -- 0xF2C: sw
  obtain ⟨n27, d27, s27, fr27, K27, W27, rg27⟩ := sv_sw F E26 s26 sv_at_f2c (off' := 0xF30) (c := 0x400)
    (by decide) (by rw [g26_2]; sv_addr) (by decide) (by decide)
  have t27 : Steps n0 n27 := t26.trans d27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keep K27 (by decide)
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rg27 sp, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg27 (3 : Fin 32), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg27 (4 : Fin 32), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg27 (8 : Fin 32), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = op15 := by rw [rg27 (9 : Fin 32), g26_9]
  have g27_10 : reg n27 a0 = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [rg27 a0, g26_10]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rg27 (18 : Fin 32), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rg27 (19 : Fin 32), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [rg27 (20 : Fin 32), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [rg27 (21 : Fin 32), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [rg27 (22 : Fin 32), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [rg27 (23 : Fin 32), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = rem := by rw [rg27 (24 : Fin 32), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [rg27 (25 : Fin 32), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = ol15 := by rw [rg27 (26 : Fin 32), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = L0 := by rw [rg27 (27 : Fin 32), g26_27]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4)] := keep_kk26.trans K27.toL
  clear keep_kk26
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K27.w32 (by decide) (by decide)).trans w26_40
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K27.w32 (by decide) (by decide)).trans w26_64
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K27.w32 (by decide) (by decide)).trans w26_7c
  have w27_25c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K27.w32 (by decide) (by decide)).trans w26_25c
  have w27_260 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K27.w32 (by decide) (by decide)).trans w26_260
  have w27_264 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K27.w32 (by decide) (by decide)).trans w26_264
  have w27_268 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K27.w32 (by decide) (by decide)).trans w26_268
  have w27_3e0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := (K27.w32 (by decide) (by decide)).trans w26_3e0
  have w27_3e4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := (K27.w32 (by decide) (by decide)).trans w26_3e4
  have w27_3e8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := (K27.w32 (by decide) (by decide)).trans w26_3e8
  have w27_3ec : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := (K27.w32 (by decide) (by decide)).trans w26_3ec
  have w27_408 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K27.w32 (by decide) (by decide)).trans w26_408
  have w27_40c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := (K27.w32 (by decide) (by decide)).trans w26_40c
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K27.w32 (by decide) (by decide)).trans w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := (K27.w32 (by decide) (by decide)).trans w26_424
  have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K27.w32 (by decide) (by decide)).trans w26_428
  have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := (K27.w32 (by decide) (by decide)).trans w26_42c
  have b27_405 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := (K27.b8 (by decide) (by decide)).trans b26_405
  have b27_406 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := (K27.b8 (by decide) (by decide)).trans b26_406
  have b27_407 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := (K27.b8 (by decide) (by decide)).trans b26_407
  have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_424
  have b27_425 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := (K27.b8 (by decide) (by decide)).trans b26_425
  have b27_426 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := (K27.b8 (by decide) (by decide)).trans b26_426
  have b27_427 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := (K27.b8 (by decide) (by decide)).trans b26_427
  have w27_400 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [W27, g26_25]
  clear b26_427 b26_426 b26_425 b26_424 b26_407 b26_406 b26_405 w26_42c w26_428 w26_424 w26_420 w26_40c w26_408 w26_3ec w26_3e8 w26_3e4 w26_3e0 w26_268 w26_264 w26_260 w26_25c w26_7c w26_64 w26_40 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0xF30: sb
  obtain ⟨n28, d28, s28, fr28, K28, W28, rg28⟩ := sv_sb F E27 s27 sv_at_f30 (off' := 0xF34) (c := 0x404)
    (by decide) (by rw [g27_2]; sv_addr) (by decide)
  have t28 : Steps n0 n28 := t27.trans d28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keep K28 (by decide)
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rg28 sp, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg28 (3 : Fin 32), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg28 (4 : Fin 32), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg28 (8 : Fin 32), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = op15 := by rw [rg28 (9 : Fin 32), g27_9]
  have g28_10 : reg n28 a0 = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [rg28 a0, g27_10]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rg28 (18 : Fin 32), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rg28 (19 : Fin 32), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [rg28 (20 : Fin 32), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [rg28 (21 : Fin 32), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [rg28 (22 : Fin 32), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [rg28 (23 : Fin 32), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = rem := by rw [rg28 (24 : Fin 32), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [rg28 (25 : Fin 32), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = ol15 := by rw [rg28 (26 : Fin 32), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = L0 := by rw [rg28 (27 : Fin 32), g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := keep_kk27.trans K28.toL
  clear keep_kk27
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K28.w32 (by decide) (by decide)).trans w27_40
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K28.w32 (by decide) (by decide)).trans w27_64
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K28.w32 (by decide) (by decide)).trans w27_7c
  have w28_25c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K28.w32 (by decide) (by decide)).trans w27_25c
  have w28_260 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K28.w32 (by decide) (by decide)).trans w27_260
  have w28_264 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K28.w32 (by decide) (by decide)).trans w27_264
  have w28_268 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K28.w32 (by decide) (by decide)).trans w27_268
  have w28_3e0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := (K28.w32 (by decide) (by decide)).trans w27_3e0
  have w28_3e4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := (K28.w32 (by decide) (by decide)).trans w27_3e4
  have w28_3e8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := (K28.w32 (by decide) (by decide)).trans w27_3e8
  have w28_3ec : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := (K28.w32 (by decide) (by decide)).trans w27_3ec
  have w28_400 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K28.w32 (by decide) (by decide)).trans w27_400
  have w28_408 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K28.w32 (by decide) (by decide)).trans w27_408
  have w28_40c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := (K28.w32 (by decide) (by decide)).trans w27_40c
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K28.w32 (by decide) (by decide)).trans w27_420
  have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := (K28.w32 (by decide) (by decide)).trans w27_424
  have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K28.w32 (by decide) (by decide)).trans w27_428
  have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := (K28.w32 (by decide) (by decide)).trans w27_42c
  have b28_405 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x405) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := (K28.b8 (by decide) (by decide)).trans b27_405
  have b28_406 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x406) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := (K28.b8 (by decide) (by decide)).trans b27_406
  have b28_407 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x407) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := (K28.b8 (by decide) (by decide)).trans b27_407
  have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_424
  have b28_425 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := (K28.b8 (by decide) (by decide)).trans b27_425
  have b28_426 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := (K28.b8 (by decide) (by decide)).trans b27_426
  have b28_427 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := (K28.b8 (by decide) (by decide)).trans b27_427
  have b28_404 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [W28, g27_8, lbu_low]
  clear w27_400 b27_427 b27_426 b27_425 b27_424 b27_407 b27_406 b27_405 w27_42c w27_428 w27_424 w27_420 w27_40c w27_408 w27_3ec w27_3e8 w27_3e4 w27_3e0 w27_268 w27_264 w27_260 w27_25c w27_7c w27_64 w27_40 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 rg27 W27 K27 fr27 s27 d27
  have w28_404 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := ld_of_bytes b28_404
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x404 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x405 by sv_addr]; exact b28_405)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x404 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x406 by sv_addr]; exact b28_406)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x404 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x407 by sv_addr]; exact b28_407)
  by_cases hrest0 : ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) = 0
  rotate_left
  · -- 0xF34: branch, taken
    obtain ⟨n29, d29, u29⟩ := s28.taken E28.self 0x14C sv_at_f34
      (by decide) (by rw [g28_10, s28.zero]; exact br_bne_t hrest0)
    have s29 : St n29.mem SV n29 0x14C (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by rw [u29.regs, g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = op15 := by rw [u29.regs, g28_9]
    have g29_10 : reg n29 a0 = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [u29.regs, g28_10]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = rem := by rw [u29.regs, g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u29.regs, g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = ol15 := by rw [u29.regs, g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = L0 := by rw [u29.regs, g28_27]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m29]; exact w28_40
    have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m29]; exact w28_64
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m29]; exact w28_7c
    have w29_25c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m29]; exact w28_25c
    have w29_260 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m29]; exact w28_260
    have w29_264 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m29]; exact w28_264
    have w29_268 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m29]; exact w28_268
    have w29_3e0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m29]; exact w28_3e0
    have w29_3e4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m29]; exact w28_3e4
    have w29_3e8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m29]; exact w28_3e8
    have w29_3ec : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m29]; exact w28_3ec
    have w29_400 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m29]; exact w28_400
    have w29_404 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m29]; exact w28_404
    have w29_408 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m29]; exact w28_408
    have w29_40c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m29]; exact w28_40c
    have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m29]; exact w28_420
    have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m29]; exact w28_424
    have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m29]; exact w28_428
    have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m29]; exact w28_42c
    have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m29]; exact b28_424
    have b29_425 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m29]; exact b28_425
    have b29_426 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m29]; exact b28_426
    have b29_427 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m29]; exact b28_427
    clear b28_404 b28_427 b28_426 b28_425 b28_424 b28_407 b28_406 b28_405 w28_42c w28_428 w28_424 w28_420 w28_40c w28_408 w28_400 w28_3ec w28_3e8 w28_3e4 w28_3e0 w28_268 w28_264 w28_260 w28_25c w28_7c w28_64 w28_40 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 rg28 W28 K28 fr28 s28 d28
    -- 0x14C
    obtain ⟨n30, c30, u30⟩ := s29.block svTra14c E29.self svTra14c_end
      ⟨trivial, trivial⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have s30 : St n30.mem SV n30 0x14E (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have rb30 : ∀ q, reg n30 q = (runBlock svTra14c (n29.mem, reg n29)).2 q := fun q => by rw [u30.regs]
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans c30
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by
      rw [rb30, runBlock_reg _ _ _ sp s29.zero (by decide), g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb30, runBlock_reg _ _ _ (3 : Fin 32) s29.zero (by decide), g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb30, runBlock_reg _ _ _ (4 : Fin 32) s29.zero (by decide), g29_4]
    have g30_9 : reg n30 (9 : Fin 32) = op15 := by
      rw [rb30, runBlock_reg _ _ _ (9 : Fin 32) s29.zero (by decide), g29_9]
    have g30_10 : reg n30 a0 = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by
      rw [rb30, runBlock_reg _ _ _ a0 s29.zero (by decide), g29_10]
    have g30_18 : reg n30 (18 : Fin 32) = out := by
      rw [rb30, runBlock_reg _ _ _ (18 : Fin 32) s29.zero (by decide), g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by
      rw [rb30, runBlock_reg _ _ _ (19 : Fin 32) s29.zero (by decide), g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = x20 := by
      rw [rb30, runBlock_reg _ _ _ (20 : Fin 32) s29.zero (by decide), g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = x21 := by
      rw [rb30, runBlock_reg _ _ _ (21 : Fin 32) s29.zero (by decide), g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = x22 := by
      rw [rb30, runBlock_reg _ _ _ (22 : Fin 32) s29.zero (by decide), g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = x23 := by
      rw [rb30, runBlock_reg _ _ _ (23 : Fin 32) s29.zero (by decide), g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = rem := by
      rw [rb30, runBlock_reg _ _ _ (24 : Fin 32) s29.zero (by decide), g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by
      rw [rb30, runBlock_reg _ _ _ (25 : Fin 32) s29.zero (by decide), g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = ol15 := by
      rw [rb30, runBlock_reg _ _ _ (26 : Fin 32) s29.zero (by decide), g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = L0 := by
      rw [rb30, runBlock_reg _ _ _ (27 : Fin 32) s29.zero (by decide), g29_27]
    have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb30]; simp +decide only [runBlock, BInstr.run, svTra14c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g29_2, g29_3, g29_4, g29_8, g29_9, g29_10, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_25, g29_26, g29_27, s29.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m30]; exact w29_40
    have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m30]; exact w29_64
    have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m30]; exact w29_7c
    have w30_25c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m30]; exact w29_25c
    have w30_260 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m30]; exact w29_260
    have w30_264 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m30]; exact w29_264
    have w30_268 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m30]; exact w29_268
    have w30_3e0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m30]; exact w29_3e0
    have w30_3e4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m30]; exact w29_3e4
    have w30_3e8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m30]; exact w29_3e8
    have w30_3ec : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m30]; exact w29_3ec
    have w30_400 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m30]; exact w29_400
    have w30_404 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m30]; exact w29_404
    have w30_408 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m30]; exact w29_408
    have w30_40c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m30]; exact w29_40c
    have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m30]; exact w29_420
    have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m30]; exact w29_424
    have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m30]; exact w29_428
    have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m30]; exact w29_42c
    have b30_424 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m30]; exact b29_424
    have b30_425 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m30]; exact b29_425
    have b30_426 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m30]; exact b29_426
    have b30_427 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m30]; exact b29_427
    clear b29_427 b29_426 b29_425 b29_424 w29_42c w29_428 w29_424 w29_420 w29_40c w29_408 w29_404 w29_400 w29_3ec w29_3e8 w29_3e4 w29_3e0 w29_268 w29_264 w29_260 w29_25c w29_7c w29_64 w29_40 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
    -- 0x14E: j
    obtain ⟨n31, d31, u31⟩ := s30.jump E30.self sv_at_14e (off' := 0x7A4) (by decide)
      (by rw [s30.pc]; decide)
    have s31 : St n31.mem SV n31 0x7A4 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, g30_4]
    have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u31.regs, g30_8]
    have g31_9 : reg n31 (9 : Fin 32) = op15 := by rw [u31.regs, g30_9]
    have g31_10 : reg n31 a0 = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [u31.regs, g30_10]
    have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [u31.regs, g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [u31.regs, g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [u31.regs, g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = rem := by rw [u31.regs, g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u31.regs, g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = ol15 := by rw [u31.regs, g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = L0 := by rw [u31.regs, g30_27]
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m31]; exact w30_40
    have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m31]; exact w30_64
    have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m31]; exact w30_7c
    have w31_25c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m31]; exact w30_25c
    have w31_260 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m31]; exact w30_260
    have w31_264 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m31]; exact w30_264
    have w31_268 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m31]; exact w30_268
    have w31_3e0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m31]; exact w30_3e0
    have w31_3e4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m31]; exact w30_3e4
    have w31_3e8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m31]; exact w30_3e8
    have w31_3ec : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m31]; exact w30_3ec
    have w31_400 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m31]; exact w30_400
    have w31_404 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m31]; exact w30_404
    have w31_408 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m31]; exact w30_408
    have w31_40c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m31]; exact w30_40c
    have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m31]; exact w30_420
    have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m31]; exact w30_424
    have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m31]; exact w30_428
    have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m31]; exact w30_42c
    have b31_424 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m31]; exact b30_424
    have b31_425 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m31]; exact b30_425
    have b31_426 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m31]; exact b30_426
    have b31_427 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m31]; exact b30_427
    clear b30_427 b30_426 b30_425 b30_424 w30_42c w30_428 w30_424 w30_420 w30_40c w30_408 w30_404 w30_400 w30_3ec w30_3e8 w30_3e4 w30_3e0 w30_268 w30_264 w30_260 w30_25c w30_7c w30_64 w30_40 g30_8 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 rb30 s30 m30 u30 c30
    exact .inl ⟨(fun ⟨h0', tl6', h1', op15', ol15', h2', to15', h3', tl20', h4', h5', _⟩ => by rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'; rw [ht15] at h3'; cases h3'; rw [hr20] at h4'; cases h4'; exact hrest0 h5'), sv_fail F E31 s31 t31 (fun x hx => (fR31 x hx).trans (fM x hx).symm) V31 hret g31_2 g31_18 hO g31_3 g31_4⟩
  -- 0xF34: branch, not taken
  obtain ⟨n29, d29, u29⟩ := s28.notTaken E28.self 0xF38 sv_at_f34
    (by decide) (by rw [g28_10, s28.zero]; exact br_bne_f hrest0)
  have s29 : St n29.mem SV n29 0xF38 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by rw [u29.regs, g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = op15 := by rw [u29.regs, g28_9]
  have g29_10 : reg n29 a0 = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [u29.regs, g28_10]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = rem := by rw [u29.regs, g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u29.regs, g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = ol15 := by rw [u29.regs, g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = L0 := by rw [u29.regs, g28_27]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m29]; exact w28_40
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m29]; exact w28_64
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m29]; exact w28_7c
  have w29_25c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m29]; exact w28_25c
  have w29_260 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m29]; exact w28_260
  have w29_264 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m29]; exact w28_264
  have w29_268 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m29]; exact w28_268
  have w29_3e0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m29]; exact w28_3e0
  have w29_3e4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m29]; exact w28_3e4
  have w29_3e8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m29]; exact w28_3e8
  have w29_3ec : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m29]; exact w28_3ec
  have w29_400 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m29]; exact w28_400
  have w29_404 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m29]; exact w28_404
  have w29_408 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m29]; exact w28_408
  have w29_40c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m29]; exact w28_40c
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m29]; exact w28_420
  have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m29]; exact w28_424
  have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m29]; exact w28_428
  have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m29]; exact w28_42c
  have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m29]; exact b28_424
  have b29_425 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m29]; exact b28_425
  have b29_426 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m29]; exact b28_426
  have b29_427 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m29]; exact b28_427
  clear b28_404 b28_427 b28_426 b28_425 b28_424 b28_407 b28_406 b28_405 w28_42c w28_428 w28_424 w28_420 w28_40c w28_408 w28_400 w28_3ec w28_3e8 w28_3e4 w28_3e0 w28_268 w28_264 w28_260 w28_25c w28_7c w28_64 w28_40 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 rg28 W28 K28 fr28 s28 d28
  -- 0xF38
  obtain ⟨n30, c30, u30⟩ := s29.block svTraf38 E29.self svTraf38_end
    ⟨trivial, trivial⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have s30 : St n30.mem SV n30 0xF3C (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have rb30 : ∀ q, reg n30 q = (runBlock svTraf38 (n29.mem, reg n29)).2 q := fun q => by rw [u30.regs]
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans c30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by
    rw [rb30, runBlock_reg _ _ _ sp s29.zero (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb30, runBlock_reg _ _ _ (3 : Fin 32) s29.zero (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb30, runBlock_reg _ _ _ (4 : Fin 32) s29.zero (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb30, runBlock_reg _ _ _ (8 : Fin 32) s29.zero (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = op15 := by
    rw [rb30, runBlock_reg _ _ _ (9 : Fin 32) s29.zero (by decide), g29_9]
  have g30_10 : reg n30 a0 = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by
    rw [rb30, runBlock_reg _ _ _ a0 s29.zero (by decide), g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by
    rw [rb30, runBlock_reg _ _ _ (18 : Fin 32) s29.zero (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by
    rw [rb30, runBlock_reg _ _ _ (19 : Fin 32) s29.zero (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by
    rw [rb30, runBlock_reg _ _ _ (20 : Fin 32) s29.zero (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by
    rw [rb30, runBlock_reg _ _ _ (21 : Fin 32) s29.zero (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by
    rw [rb30, runBlock_reg _ _ _ (22 : Fin 32) s29.zero (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by
    rw [rb30, runBlock_reg _ _ _ (23 : Fin 32) s29.zero (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = rem := by
    rw [rb30, runBlock_reg _ _ _ (24 : Fin 32) s29.zero (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by
    rw [rb30, runBlock_reg _ _ _ (25 : Fin 32) s29.zero (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = ol15 := by
    rw [rb30, runBlock_reg _ _ _ (26 : Fin 32) s29.zero (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = L0 := by
    rw [rb30, runBlock_reg _ _ _ (27 : Fin 32) s29.zero (by decide), g29_27]
  have g30_11 : reg n30 a1 = (L0) - (rem) := by
    rw [rb30]; simp +decide only [runBlock, BInstr.run, svTraf38, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g29_2, g29_3, g29_4, g29_8, g29_9, g29_10, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_25, g29_26, g29_27, s29.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m30]; exact w29_40
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m30]; exact w29_64
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m30]; exact w29_7c
  have w30_25c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m30]; exact w29_25c
  have w30_260 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m30]; exact w29_260
  have w30_264 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m30]; exact w29_264
  have w30_268 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m30]; exact w29_268
  have w30_3e0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m30]; exact w29_3e0
  have w30_3e4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m30]; exact w29_3e4
  have w30_3e8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m30]; exact w29_3e8
  have w30_3ec : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m30]; exact w29_3ec
  have w30_400 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m30]; exact w29_400
  have w30_404 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m30]; exact w29_404
  have w30_408 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m30]; exact w29_408
  have w30_40c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m30]; exact w29_40c
  have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m30]; exact w29_420
  have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m30]; exact w29_424
  have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m30]; exact w29_428
  have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m30]; exact w29_42c
  have b30_424 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m30]; exact b29_424
  have b30_425 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m30]; exact b29_425
  have b30_426 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m30]; exact b29_426
  have b30_427 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m30]; exact b29_427
  clear b29_427 b29_426 b29_425 b29_424 w29_42c w29_428 w29_424 w29_420 w29_40c w29_408 w29_404 w29_400 w29_3ec w29_3e8 w29_3e4 w29_3e0 w29_268 w29_264 w29_260 w29_25c w29_7c w29_64 w29_40 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29 w28_404
  -- 0xF3C: lw
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_f3c (off' := 0xF3E) (by decide)
    (by rw [g30_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s31 : St n31.mem SV n31 0xF3E (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = op15 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
  have g31_11 : reg n31 a1 = (L0) - (rem) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_11]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = rem := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = ol15 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = L0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
  have g31_10 : reg n31 a0 = p0 := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr, w30_40]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m31]; exact w30_40
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m31]; exact w30_64
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m31]; exact w30_7c
  have w31_25c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m31]; exact w30_25c
  have w31_260 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m31]; exact w30_260
  have w31_264 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m31]; exact w30_264
  have w31_268 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m31]; exact w30_268
  have w31_3e0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m31]; exact w30_3e0
  have w31_3e4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m31]; exact w30_3e4
  have w31_3e8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m31]; exact w30_3e8
  have w31_3ec : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m31]; exact w30_3ec
  have w31_400 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m31]; exact w30_400
  have w31_404 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m31]; exact w30_404
  have w31_408 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m31]; exact w30_408
  have w31_40c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m31]; exact w30_40c
  have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m31]; exact w30_420
  have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m31]; exact w30_424
  have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m31]; exact w30_428
  have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m31]; exact w30_42c
  have b31_424 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m31]; exact b30_424
  have b31_425 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m31]; exact b30_425
  have b31_426 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m31]; exact b30_426
  have b31_427 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m31]; exact b30_427
  clear b30_427 b30_426 b30_425 b30_424 w30_42c w30_428 w30_424 w30_420 w30_40c w30_408 w30_404 w30_400 w30_3ec w30_3e8 w30_3e4 w30_3e0 w30_268 w30_264 w30_260 w30_25c w30_7c w30_64 w30_40 g30_11 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 rb30 s30 m30 u30 c30
  -- 0xF3E
  obtain ⟨n32, c32, u32⟩ := s31.block svTraf3e E31.self svTraf3e_end
    ⟨trivial, trivial, trivial⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have s32 : St n32.mem SV n32 0xF42 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have rb32 : ∀ q, reg n32 q = (runBlock svTraf3e (n31.mem, reg n31)).2 q := fun q => by rw [u32.regs]
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans c32
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by
    rw [rb32, runBlock_reg _ _ _ sp s31.zero (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb32, runBlock_reg _ _ _ (3 : Fin 32) s31.zero (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb32, runBlock_reg _ _ _ (4 : Fin 32) s31.zero (by decide), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb32, runBlock_reg _ _ _ (8 : Fin 32) s31.zero (by decide), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = op15 := by
    rw [rb32, runBlock_reg _ _ _ (9 : Fin 32) s31.zero (by decide), g31_9]
  have g32_10 : reg n32 a0 = p0 := by
    rw [rb32, runBlock_reg _ _ _ a0 s31.zero (by decide), g31_10]
  have g32_11 : reg n32 a1 = (L0) - (rem) := by
    rw [rb32, runBlock_reg _ _ _ a1 s31.zero (by decide), g31_11]
  have g32_18 : reg n32 (18 : Fin 32) = out := by
    rw [rb32, runBlock_reg _ _ _ (18 : Fin 32) s31.zero (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by
    rw [rb32, runBlock_reg _ _ _ (19 : Fin 32) s31.zero (by decide), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = x20 := by
    rw [rb32, runBlock_reg _ _ _ (20 : Fin 32) s31.zero (by decide), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by
    rw [rb32, runBlock_reg _ _ _ (21 : Fin 32) s31.zero (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = x22 := by
    rw [rb32, runBlock_reg _ _ _ (22 : Fin 32) s31.zero (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = x23 := by
    rw [rb32, runBlock_reg _ _ _ (23 : Fin 32) s31.zero (by decide), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = rem := by
    rw [rb32, runBlock_reg _ _ _ (24 : Fin 32) s31.zero (by decide), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by
    rw [rb32, runBlock_reg _ _ _ (25 : Fin 32) s31.zero (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = ol15 := by
    rw [rb32, runBlock_reg _ _ _ (26 : Fin 32) s31.zero (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = L0 := by
    rw [rb32, runBlock_reg _ _ _ (27 : Fin 32) s31.zero (by decide), g31_27]
  have g32_12 : reg n32 a2 = op15 := by
    rw [rb32]; simp +decide only [runBlock, BInstr.run, svTraf3e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g31_2, g31_3, g31_4, g31_8, g31_9, g31_10, g31_11, g31_18, g31_19, g31_20, g31_21, g31_22, g31_23, g31_24, g31_25, g31_26, g31_27, s31.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g32_13 : reg n32 a3 = ol15 := by
    rw [rb32]; simp +decide only [runBlock, BInstr.run, svTraf3e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g31_2, g31_3, g31_4, g31_8, g31_9, g31_10, g31_11, g31_18, g31_19, g31_20, g31_21, g31_22, g31_23, g31_24, g31_25, g31_26, g31_27, s31.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m32]; exact w31_40
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m32]; exact w31_64
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m32]; exact w31_7c
  have w32_25c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m32]; exact w31_25c
  have w32_260 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m32]; exact w31_260
  have w32_264 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m32]; exact w31_264
  have w32_268 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m32]; exact w31_268
  have w32_3e0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m32]; exact w31_3e0
  have w32_3e4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m32]; exact w31_3e4
  have w32_3e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m32]; exact w31_3e8
  have w32_3ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m32]; exact w31_3ec
  have w32_400 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m32]; exact w31_400
  have w32_404 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m32]; exact w31_404
  have w32_408 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m32]; exact w31_408
  have w32_40c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m32]; exact w31_40c
  have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m32]; exact w31_420
  have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m32]; exact w31_424
  have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m32]; exact w31_428
  have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m32]; exact w31_42c
  have b32_424 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m32]; exact b31_424
  have b32_425 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m32]; exact b31_425
  have b32_426 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m32]; exact b31_426
  have b32_427 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m32]; exact b31_427
  clear b31_427 b31_426 b31_425 b31_424 w31_42c w31_428 w31_424 w31_420 w31_40c w31_408 w31_404 w31_400 w31_3ec w31_3e8 w31_3e4 w31_3e0 w31_268 w31_264 w31_260 w31_25c w31_7c w31_64 w31_40 g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_11 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0xF42: sv_loF
  obtain ⟨n33, c33, s33, sp33, rk33, R33, K33, fr33⟩ := sv_loF (nl := ((L0) - (rem)).toNat) (ql := ol15.toNat)
    F E32 s32 sv_at_f42 sv_at_f46 (by decide) (by decide) g32_2
    g32_10 (by rw [g32_11, ofNat_toNat_self]) g32_12 (by rw [g32_13, ofNat_toNat_self]) (p0_in.shrink (sub_le_toNat hle)) ((cr_in.contentW hr6).oidIn hr15)
  have t33 : Steps n0 n33 := t32.trans c33
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.keepL K33 (by decide)
  rw [listsOidOf, listsOidLoop_congr _ _ _ (sv_pt fR32 (p0_in.shrink (sub_le_toNat hle))), sv_mb fR32 ((cr_in.contentW hr6).oidIn hr15), ← listsOidOf] at R33
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk33 (3 : Fin 32) (by decide), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk33 (4 : Fin 32) (by decide), g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = ((BitVec.ofNat 32 tl20.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk33 (8 : Fin 32) (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = op15 := by rw [rk33 (9 : Fin 32) (by decide), g32_9]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [rk33 (18 : Fin 32) (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [rk33 (19 : Fin 32) (by decide), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = x20 := by rw [rk33 (20 : Fin 32) (by decide), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = x21 := by rw [rk33 (21 : Fin 32) (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = x22 := by rw [rk33 (22 : Fin 32) (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = x23 := by rw [rk33 (23 : Fin 32) (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = rem := by rw [rk33 (24 : Fin 32) (by decide), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [rk33 (25 : Fin 32) (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = ol15 := by rw [rk33 (26 : Fin 32) (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = L0 := by rw [rk33 (27 : Fin 32) (by decide), g32_27]
  have g33_2 : reg n33 sp = B + 0x21A0 := sp33
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := keep_kk32.trans K33
  clear keep_kk32
  have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := (K33.w32 (by decide) (by decide)).trans w32_40
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K33.w32 (by decide) (by decide)).trans w32_64
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K33.w32 (by decide) (by decide)).trans w32_7c
  have w33_25c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K33.w32 (by decide) (by decide)).trans w32_25c
  have w33_260 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K33.w32 (by decide) (by decide)).trans w32_260
  have w33_264 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K33.w32 (by decide) (by decide)).trans w32_264
  have w33_268 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K33.w32 (by decide) (by decide)).trans w32_268
  have w33_3e0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := (K33.w32 (by decide) (by decide)).trans w32_3e0
  have w33_3e4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := (K33.w32 (by decide) (by decide)).trans w32_3e4
  have w33_3e8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := (K33.w32 (by decide) (by decide)).trans w32_3e8
  have w33_3ec : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := (K33.w32 (by decide) (by decide)).trans w32_3ec
  have w33_400 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K33.w32 (by decide) (by decide)).trans w32_400
  have w33_404 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := (K33.w32 (by decide) (by decide)).trans w32_404
  have w33_408 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K33.w32 (by decide) (by decide)).trans w32_408
  have w33_40c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := (K33.w32 (by decide) (by decide)).trans w32_40c
  have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K33.w32 (by decide) (by decide)).trans w32_420
  have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := (K33.w32 (by decide) (by decide)).trans w32_424
  have w33_428 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := (K33.w32 (by decide) (by decide)).trans w32_428
  have w33_42c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := (K33.w32 (by decide) (by decide)).trans w32_42c
  have b33_424 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := (K33.b8 (by decide) (by decide)).trans b32_424
  have b33_425 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := (K33.b8 (by decide) (by decide)).trans b32_425
  have b33_426 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := (K33.b8 (by decide) (by decide)).trans b32_426
  have b33_427 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := (K33.b8 (by decide) (by decide)).trans b32_427
  clear b32_427 b32_426 b32_425 b32_424 w32_42c w32_428 w32_424 w32_420 w32_40c w32_408 w32_404 w32_400 w32_3ec w32_3e8 w32_3e4 w32_3e0 w32_268 w32_264 w32_260 w32_25c w32_7c w32_64 w32_40 g32_13 g32_12 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 rb32 s32 m32 u32 c32
  obtain ⟨r33, hr33⟩ : ∃ r, listsOidOf M0 p0 ((L0) - (rem)).toNat (memBytes M0 op15 ol15.toNat) = r := ⟨_, rfl⟩
  rcases r33 with b33 | (_ | _)
  · rw [hr33] at R33
    obtain ⟨a0_33, a1_33⟩ := R33
    have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x1 := a0_33
    -- 0xF4A
    obtain ⟨n34, c34, u34⟩ := s33.block svTraf4a E33.self svTraf4a_end
      ⟨trivial, trivial, trivial⟩
    have m34 : n34.mem = n33.mem := u34.mem
    have s34 : St n34.mem SV n34 0xF4E (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
    have rb34 : ∀ q, reg n34 q = (runBlock svTraf4a (n33.mem, reg n33)).2 q := fun q => by rw [u34.regs]
    have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
    have t34 : Steps n0 n34 := t33.trans c34
    have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.same m34
    have g34_2 : reg n34 sp = B + 0x21A0 := by
      rw [rb34, runBlock_reg _ _ _ sp s33.zero (by decide), g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb34, runBlock_reg _ _ _ (3 : Fin 32) s33.zero (by decide), g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb34, runBlock_reg _ _ _ (4 : Fin 32) s33.zero (by decide), g33_4]
    have g34_9 : reg n34 (9 : Fin 32) = op15 := by
      rw [rb34, runBlock_reg _ _ _ (9 : Fin 32) s33.zero (by decide), g33_9]
    have g34_18 : reg n34 (18 : Fin 32) = out := by
      rw [rb34, runBlock_reg _ _ _ (18 : Fin 32) s33.zero (by decide), g33_18]
    have g34_19 : reg n34 (19 : Fin 32) = bp := by
      rw [rb34, runBlock_reg _ _ _ (19 : Fin 32) s33.zero (by decide), g33_19]
    have g34_20 : reg n34 (20 : Fin 32) = x20 := by
      rw [rb34, runBlock_reg _ _ _ (20 : Fin 32) s33.zero (by decide), g33_20]
    have g34_21 : reg n34 (21 : Fin 32) = x21 := by
      rw [rb34, runBlock_reg _ _ _ (21 : Fin 32) s33.zero (by decide), g33_21]
    have g34_22 : reg n34 (22 : Fin 32) = x22 := by
      rw [rb34, runBlock_reg _ _ _ (22 : Fin 32) s33.zero (by decide), g33_22]
    have g34_23 : reg n34 (23 : Fin 32) = x23 := by
      rw [rb34, runBlock_reg _ _ _ (23 : Fin 32) s33.zero (by decide), g33_23]
    have g34_24 : reg n34 (24 : Fin 32) = rem := by
      rw [rb34, runBlock_reg _ _ _ (24 : Fin 32) s33.zero (by decide), g33_24]
    have g34_25 : reg n34 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by
      rw [rb34, runBlock_reg _ _ _ (25 : Fin 32) s33.zero (by decide), g33_25]
    have g34_26 : reg n34 (26 : Fin 32) = ol15 := by
      rw [rb34, runBlock_reg _ _ _ (26 : Fin 32) s33.zero (by decide), g33_26]
    have g34_27 : reg n34 (27 : Fin 32) = L0 := by
      rw [rb34, runBlock_reg _ _ _ (27 : Fin 32) s33.zero (by decide), g33_27]
    have g34_10 : reg n34 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb34]; simp +decide only [runBlock, BInstr.run, svTraf4a, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_10, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m34]; exact keep_kk33
    clear keep_kk33
    have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m34]; exact w33_40
    have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m34]; exact w33_64
    have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m34]; exact w33_7c
    have w34_25c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m34]; exact w33_25c
    have w34_260 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m34]; exact w33_260
    have w34_264 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m34]; exact w33_264
    have w34_268 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m34]; exact w33_268
    have w34_3e0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m34]; exact w33_3e0
    have w34_3e4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m34]; exact w33_3e4
    have w34_3e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m34]; exact w33_3e8
    have w34_3ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m34]; exact w33_3ec
    have w34_400 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_400
    have w34_404 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_404
    have w34_408 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_408
    have w34_40c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_40c
    have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_420
    have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_424
    have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_428
    have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_42c
    have b34_424 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m34]; exact b33_424
    have b34_425 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m34]; exact b33_425
    have b34_426 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m34]; exact b33_426
    have b34_427 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m34]; exact b33_427
    clear b33_427 b33_426 b33_425 b33_424 w33_42c w33_428 w33_424 w33_420 w33_40c w33_408 w33_404 w33_400 w33_3ec w33_3e8 w33_3e4 w33_3e0 w33_268 w33_264 w33_260 w33_25c w33_7c w33_64 w33_40 g33_2 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 V33 E33 fR33 t33 fr33 K33 rk33 sp33 s33 c33
    -- 0xF4E: branch, taken
    obtain ⟨n35, d35, u35⟩ := s34.taken E34.self 0x7A4 sv_at_f4e
      (by decide) (by rw [g34_10, s34.zero]; decide)
    have s35 : St n35.mem SV n35 0x7A4 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
    have m35 : n35.mem = n34.mem := u35.mem
    have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
    have t35 : Steps n0 n35 := t34.trans (.single d35)
    have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
    have E35 : SvCode n35.mem := E34.fr F fr35
    have V35 : SvSaves B n35.mem v := V34.same m35
    have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, g34_2]
    have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, g34_3]
    have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, g34_4]
    have g35_9 : reg n35 (9 : Fin 32) = op15 := by rw [u35.regs, g34_9]
    have g35_10 : reg n35 a0 = BitVec.ofNat 32 0x1 := by rw [u35.regs, g34_10]
    have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
    have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
    have g35_20 : reg n35 (20 : Fin 32) = x20 := by rw [u35.regs, g34_20]
    have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [u35.regs, g34_21]
    have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [u35.regs, g34_22]
    have g35_23 : reg n35 (23 : Fin 32) = x23 := by rw [u35.regs, g34_23]
    have g35_24 : reg n35 (24 : Fin 32) = rem := by rw [u35.regs, g34_24]
    have g35_25 : reg n35 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u35.regs, g34_25]
    have g35_26 : reg n35 (26 : Fin 32) = ol15 := by rw [u35.regs, g34_26]
    have g35_27 : reg n35 (27 : Fin 32) = L0 := by rw [u35.regs, g34_27]
    have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m35]; exact keep_kk34
    clear keep_kk34
    have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m35]; exact w34_40
    have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m35]; exact w34_64
    have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m35]; exact w34_7c
    have w35_25c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m35]; exact w34_25c
    have w35_260 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m35]; exact w34_260
    have w35_264 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m35]; exact w34_264
    have w35_268 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m35]; exact w34_268
    have w35_3e0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m35]; exact w34_3e0
    have w35_3e4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m35]; exact w34_3e4
    have w35_3e8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m35]; exact w34_3e8
    have w35_3ec : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m35]; exact w34_3ec
    have w35_400 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_400
    have w35_404 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_404
    have w35_408 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_408
    have w35_40c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_40c
    have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_420
    have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_424
    have w35_428 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_428
    have w35_42c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_42c
    have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m35]; exact b34_424
    have b35_425 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m35]; exact b34_425
    have b35_426 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m35]; exact b34_426
    have b35_427 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m35]; exact b34_427
    clear b34_427 b34_426 b34_425 b34_424 w34_42c w34_428 w34_424 w34_420 w34_40c w34_408 w34_404 w34_400 w34_3ec w34_3e8 w34_3e4 w34_3e0 w34_268 w34_264 w34_260 w34_25c w34_7c w34_64 w34_40 g34_10 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34 g33_10 a1_33 a0_33
    exact .inl ⟨(fun ⟨h0', tl6', h1', op15', ol15', h2', to15', h3', tl20', h4', h5', h6', _⟩ => by rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'; rw [ht15] at h3'; cases h3'; rw [hr20] at h4'; cases h4'; rw [hr33] at h6'; cases h6'), sv_fail F E35 s35 t35 (fun x hx => (fR35 x hx).trans (fM x hx).symm) V35 hret g35_2 g35_18 hO g35_3 g35_4⟩
  rotate_left
  · rw [hr33] at R33
    obtain ⟨a0_33, a1_33⟩ := R33
    have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x0 := a0_33
    have g33_11 : reg n33 a1 = BitVec.ofNat 32 0x1 := by rw [a1_33]; rfl
    -- 0xF4A
    obtain ⟨n34, c34, u34⟩ := s33.block svTraf4a E33.self svTraf4a_end
      ⟨trivial, trivial, trivial⟩
    have m34 : n34.mem = n33.mem := u34.mem
    have s34 : St n34.mem SV n34 0xF4E (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
    have rb34 : ∀ q, reg n34 q = (runBlock svTraf4a (n33.mem, reg n33)).2 q := fun q => by rw [u34.regs]
    have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
    have t34 : Steps n0 n34 := t33.trans c34
    have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.same m34
    have g34_2 : reg n34 sp = B + 0x21A0 := by
      rw [rb34, runBlock_reg _ _ _ sp s33.zero (by decide), g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb34, runBlock_reg _ _ _ (3 : Fin 32) s33.zero (by decide), g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb34, runBlock_reg _ _ _ (4 : Fin 32) s33.zero (by decide), g33_4]
    have g34_9 : reg n34 (9 : Fin 32) = op15 := by
      rw [rb34, runBlock_reg _ _ _ (9 : Fin 32) s33.zero (by decide), g33_9]
    have g34_11 : reg n34 a1 = BitVec.ofNat 32 0x1 := by
      rw [rb34, runBlock_reg _ _ _ a1 s33.zero (by decide), g33_11]
    have g34_18 : reg n34 (18 : Fin 32) = out := by
      rw [rb34, runBlock_reg _ _ _ (18 : Fin 32) s33.zero (by decide), g33_18]
    have g34_19 : reg n34 (19 : Fin 32) = bp := by
      rw [rb34, runBlock_reg _ _ _ (19 : Fin 32) s33.zero (by decide), g33_19]
    have g34_20 : reg n34 (20 : Fin 32) = x20 := by
      rw [rb34, runBlock_reg _ _ _ (20 : Fin 32) s33.zero (by decide), g33_20]
    have g34_21 : reg n34 (21 : Fin 32) = x21 := by
      rw [rb34, runBlock_reg _ _ _ (21 : Fin 32) s33.zero (by decide), g33_21]
    have g34_22 : reg n34 (22 : Fin 32) = x22 := by
      rw [rb34, runBlock_reg _ _ _ (22 : Fin 32) s33.zero (by decide), g33_22]
    have g34_23 : reg n34 (23 : Fin 32) = x23 := by
      rw [rb34, runBlock_reg _ _ _ (23 : Fin 32) s33.zero (by decide), g33_23]
    have g34_24 : reg n34 (24 : Fin 32) = rem := by
      rw [rb34, runBlock_reg _ _ _ (24 : Fin 32) s33.zero (by decide), g33_24]
    have g34_25 : reg n34 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by
      rw [rb34, runBlock_reg _ _ _ (25 : Fin 32) s33.zero (by decide), g33_25]
    have g34_26 : reg n34 (26 : Fin 32) = ol15 := by
      rw [rb34, runBlock_reg _ _ _ (26 : Fin 32) s33.zero (by decide), g33_26]
    have g34_27 : reg n34 (27 : Fin 32) = L0 := by
      rw [rb34, runBlock_reg _ _ _ (27 : Fin 32) s33.zero (by decide), g33_27]
    have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb34]; simp +decide only [runBlock, BInstr.run, svTraf4a, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_10, g33_11, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g34_10 : reg n34 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb34]; simp +decide only [runBlock, BInstr.run, svTraf4a, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_10, g33_11, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m34]; exact keep_kk33
    clear keep_kk33
    have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m34]; exact w33_40
    have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m34]; exact w33_64
    have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m34]; exact w33_7c
    have w34_25c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m34]; exact w33_25c
    have w34_260 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m34]; exact w33_260
    have w34_264 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m34]; exact w33_264
    have w34_268 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m34]; exact w33_268
    have w34_3e0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m34]; exact w33_3e0
    have w34_3e4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m34]; exact w33_3e4
    have w34_3e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m34]; exact w33_3e8
    have w34_3ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m34]; exact w33_3ec
    have w34_400 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_400
    have w34_404 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_404
    have w34_408 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_408
    have w34_40c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_40c
    have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_420
    have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_424
    have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_428
    have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_42c
    have b34_424 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m34]; exact b33_424
    have b34_425 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m34]; exact b33_425
    have b34_426 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m34]; exact b33_426
    have b34_427 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m34]; exact b33_427
    clear b33_427 b33_426 b33_425 b33_424 w33_42c w33_428 w33_424 w33_420 w33_40c w33_408 w33_404 w33_400 w33_3ec w33_3e8 w33_3e4 w33_3e0 w33_268 w33_264 w33_260 w33_25c w33_7c w33_64 w33_40 g33_2 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 V33 E33 fR33 t33 fr33 K33 rk33 sp33 s33 c33
    -- 0xF4E: branch, not taken
    obtain ⟨n35, d35, u35⟩ := s34.notTaken E34.self 0xF52 sv_at_f4e
      (by decide) (by rw [g34_10, s34.zero]; decide)
    have s35 : St n35.mem SV n35 0xF52 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
    have m35 : n35.mem = n34.mem := u35.mem
    have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
    have t35 : Steps n0 n35 := t34.trans (.single d35)
    have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
    have E35 : SvCode n35.mem := E34.fr F fr35
    have V35 : SvSaves B n35.mem v := V34.same m35
    have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, g34_2]
    have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, g34_3]
    have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, g34_4]
    have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u35.regs, g34_8]
    have g35_9 : reg n35 (9 : Fin 32) = op15 := by rw [u35.regs, g34_9]
    have g35_10 : reg n35 a0 = BitVec.ofNat 32 0x0 := by rw [u35.regs, g34_10]
    have g35_11 : reg n35 a1 = BitVec.ofNat 32 0x1 := by rw [u35.regs, g34_11]
    have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
    have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
    have g35_20 : reg n35 (20 : Fin 32) = x20 := by rw [u35.regs, g34_20]
    have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [u35.regs, g34_21]
    have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [u35.regs, g34_22]
    have g35_23 : reg n35 (23 : Fin 32) = x23 := by rw [u35.regs, g34_23]
    have g35_24 : reg n35 (24 : Fin 32) = rem := by rw [u35.regs, g34_24]
    have g35_25 : reg n35 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u35.regs, g34_25]
    have g35_26 : reg n35 (26 : Fin 32) = ol15 := by rw [u35.regs, g34_26]
    have g35_27 : reg n35 (27 : Fin 32) = L0 := by rw [u35.regs, g34_27]
    have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m35]; exact keep_kk34
    clear keep_kk34
    have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m35]; exact w34_40
    have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m35]; exact w34_64
    have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m35]; exact w34_7c
    have w35_25c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m35]; exact w34_25c
    have w35_260 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m35]; exact w34_260
    have w35_264 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m35]; exact w34_264
    have w35_268 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m35]; exact w34_268
    have w35_3e0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m35]; exact w34_3e0
    have w35_3e4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m35]; exact w34_3e4
    have w35_3e8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m35]; exact w34_3e8
    have w35_3ec : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m35]; exact w34_3ec
    have w35_400 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_400
    have w35_404 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_404
    have w35_408 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_408
    have w35_40c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_40c
    have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_420
    have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_424
    have w35_428 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_428
    have w35_42c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_42c
    have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m35]; exact b34_424
    have b35_425 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m35]; exact b34_425
    have b35_426 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m35]; exact b34_426
    have b35_427 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m35]; exact b34_427
    clear b34_427 b34_426 b34_425 b34_424 w34_42c w34_428 w34_424 w34_420 w34_40c w34_408 w34_404 w34_400 w34_3ec w34_3e8 w34_3e4 w34_3e0 w34_268 w34_264 w34_260 w34_25c w34_7c w34_64 w34_40 g34_10 g34_8 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_11 g34_9 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34 g33_11 g33_10 a1_33 a0_33
    -- 0xF52
    obtain ⟨n36, c36, u36⟩ := s35.block svTraf52 E35.self svTraf52_end
      ⟨trivial, trivial, trivial⟩
    have m36 : n36.mem = n35.mem := u36.mem
    have s36 : St n36.mem SV n36 0xF58 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
    have rb36 : ∀ q, reg n36 q = (runBlock svTraf52 (n35.mem, reg n35)).2 q := fun q => by rw [u36.regs]
    have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
    have t36 : Steps n0 n36 := t35.trans c36
    have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
    have E36 : SvCode n36.mem := E35.fr F fr36
    have V36 : SvSaves B n36.mem v := V35.same m36
    have g36_2 : reg n36 sp = B + 0x21A0 := by
      rw [rb36, runBlock_reg _ _ _ sp s35.zero (by decide), g35_2]
    have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb36, runBlock_reg _ _ _ (3 : Fin 32) s35.zero (by decide), g35_3]
    have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb36, runBlock_reg _ _ _ (4 : Fin 32) s35.zero (by decide), g35_4]
    have g36_9 : reg n36 (9 : Fin 32) = op15 := by
      rw [rb36, runBlock_reg _ _ _ (9 : Fin 32) s35.zero (by decide), g35_9]
    have g36_11 : reg n36 a1 = BitVec.ofNat 32 0x1 := by
      rw [rb36, runBlock_reg _ _ _ a1 s35.zero (by decide), g35_11]
    have g36_18 : reg n36 (18 : Fin 32) = out := by
      rw [rb36, runBlock_reg _ _ _ (18 : Fin 32) s35.zero (by decide), g35_18]
    have g36_19 : reg n36 (19 : Fin 32) = bp := by
      rw [rb36, runBlock_reg _ _ _ (19 : Fin 32) s35.zero (by decide), g35_19]
    have g36_20 : reg n36 (20 : Fin 32) = x20 := by
      rw [rb36, runBlock_reg _ _ _ (20 : Fin 32) s35.zero (by decide), g35_20]
    have g36_21 : reg n36 (21 : Fin 32) = x21 := by
      rw [rb36, runBlock_reg _ _ _ (21 : Fin 32) s35.zero (by decide), g35_21]
    have g36_22 : reg n36 (22 : Fin 32) = x22 := by
      rw [rb36, runBlock_reg _ _ _ (22 : Fin 32) s35.zero (by decide), g35_22]
    have g36_23 : reg n36 (23 : Fin 32) = x23 := by
      rw [rb36, runBlock_reg _ _ _ (23 : Fin 32) s35.zero (by decide), g35_23]
    have g36_24 : reg n36 (24 : Fin 32) = rem := by
      rw [rb36, runBlock_reg _ _ _ (24 : Fin 32) s35.zero (by decide), g35_24]
    have g36_25 : reg n36 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by
      rw [rb36, runBlock_reg _ _ _ (25 : Fin 32) s35.zero (by decide), g35_25]
    have g36_26 : reg n36 (26 : Fin 32) = ol15 := by
      rw [rb36, runBlock_reg _ _ _ (26 : Fin 32) s35.zero (by decide), g35_26]
    have g36_27 : reg n36 (27 : Fin 32) = L0 := by
      rw [rb36, runBlock_reg _ _ _ (27 : Fin 32) s35.zero (by decide), g35_27]
    have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb36]; simp +decide only [runBlock, BInstr.run, svTraf52, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_10, g35_11, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, s35.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g36_10 : reg n36 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb36]; simp +decide only [runBlock, BInstr.run, svTraf52, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_10, g35_11, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, s35.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m36]; exact keep_kk35
    clear keep_kk35
    have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m36]; exact w35_40
    have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m36]; exact w35_64
    have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m36]; exact w35_7c
    have w36_25c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m36]; exact w35_25c
    have w36_260 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m36]; exact w35_260
    have w36_264 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m36]; exact w35_264
    have w36_268 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m36]; exact w35_268
    have w36_3e0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m36]; exact w35_3e0
    have w36_3e4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m36]; exact w35_3e4
    have w36_3e8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m36]; exact w35_3e8
    have w36_3ec : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m36]; exact w35_3ec
    have w36_400 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m36]; exact w35_400
    have w36_404 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m36]; exact w35_404
    have w36_408 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m36]; exact w35_408
    have w36_40c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m36]; exact w35_40c
    have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m36]; exact w35_420
    have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m36]; exact w35_424
    have w36_428 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m36]; exact w35_428
    have w36_42c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m36]; exact w35_42c
    have b36_424 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m36]; exact b35_424
    have b36_425 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m36]; exact b35_425
    have b36_426 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m36]; exact b35_426
    have b36_427 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m36]; exact b35_427
    clear b35_427 b35_426 b35_425 b35_424 w35_42c w35_428 w35_424 w35_420 w35_40c w35_408 w35_404 w35_400 w35_3ec w35_3e8 w35_3e4 w35_3e0 w35_268 w35_264 w35_260 w35_25c w35_7c w35_64 w35_40 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_11 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
    -- 0xF58: branch, taken
    obtain ⟨n37, d37, u37⟩ := s36.taken E36.self 0x7A4 sv_at_f58
      (by decide) (by rw [g36_10, s36.zero]; decide)
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
    have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u37.regs, g36_8]
    have g37_9 : reg n37 (9 : Fin 32) = op15 := by rw [u37.regs, g36_9]
    have g37_10 : reg n37 a0 = BitVec.ofNat 32 0x1 := by rw [u37.regs, g36_10]
    have g37_11 : reg n37 a1 = BitVec.ofNat 32 0x1 := by rw [u37.regs, g36_11]
    have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
    have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
    have g37_20 : reg n37 (20 : Fin 32) = x20 := by rw [u37.regs, g36_20]
    have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [u37.regs, g36_21]
    have g37_22 : reg n37 (22 : Fin 32) = x22 := by rw [u37.regs, g36_22]
    have g37_23 : reg n37 (23 : Fin 32) = x23 := by rw [u37.regs, g36_23]
    have g37_24 : reg n37 (24 : Fin 32) = rem := by rw [u37.regs, g36_24]
    have g37_25 : reg n37 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u37.regs, g36_25]
    have g37_26 : reg n37 (26 : Fin 32) = ol15 := by rw [u37.regs, g36_26]
    have g37_27 : reg n37 (27 : Fin 32) = L0 := by rw [u37.regs, g36_27]
    have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m37]; exact keep_kk36
    clear keep_kk36
    have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m37]; exact w36_40
    have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m37]; exact w36_64
    have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m37]; exact w36_7c
    have w37_25c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m37]; exact w36_25c
    have w37_260 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m37]; exact w36_260
    have w37_264 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m37]; exact w36_264
    have w37_268 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m37]; exact w36_268
    have w37_3e0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m37]; exact w36_3e0
    have w37_3e4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m37]; exact w36_3e4
    have w37_3e8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m37]; exact w36_3e8
    have w37_3ec : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m37]; exact w36_3ec
    have w37_400 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m37]; exact w36_400
    have w37_404 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m37]; exact w36_404
    have w37_408 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m37]; exact w36_408
    have w37_40c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m37]; exact w36_40c
    have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m37]; exact w36_420
    have w37_424 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m37]; exact w36_424
    have w37_428 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m37]; exact w36_428
    have w37_42c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m37]; exact w36_42c
    have b37_424 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m37]; exact b36_424
    have b37_425 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m37]; exact b36_425
    have b37_426 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m37]; exact b36_426
    have b37_427 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m37]; exact b36_427
    clear b36_427 b36_426 b36_425 b36_424 w36_42c w36_428 w36_424 w36_420 w36_40c w36_408 w36_404 w36_400 w36_3ec w36_3e8 w36_3e4 w36_3e0 w36_268 w36_264 w36_260 w36_25c w36_7c w36_64 w36_40 g36_10 g36_8 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_11 g36_9 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 rb36 s36 m36 u36 c36
    exact .inl ⟨(fun ⟨h0', tl6', h1', op15', ol15', h2', to15', h3', tl20', h4', h5', h6', _⟩ => by rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'; rw [ht15] at h3'; cases h3'; rw [hr20] at h4'; cases h4'; rw [hr33] at h6'; cases h6'), sv_fail F E37 s37 t37 (fun x hx => (fR37 x hx).trans (fM x hx).symm) V37 hret g37_2 g37_18 hO g37_3 g37_4⟩
  rw [hr33] at R33
  obtain ⟨a0_33, a1_33⟩ := R33
  have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x0 := a0_33
  have g33_11 : reg n33 a1 = BitVec.ofNat 32 0x0 := by rw [a1_33]; rfl
  -- 0xF4A
  obtain ⟨n34, c34, u34⟩ := s33.block svTraf4a E33.self svTraf4a_end
    ⟨trivial, trivial, trivial⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have s34 : St n34.mem SV n34 0xF4E (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have rb34 : ∀ q, reg n34 q = (runBlock svTraf4a (n33.mem, reg n33)).2 q := fun q => by rw [u34.regs]
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans c34
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by
    rw [rb34, runBlock_reg _ _ _ sp s33.zero (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb34, runBlock_reg _ _ _ (3 : Fin 32) s33.zero (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb34, runBlock_reg _ _ _ (4 : Fin 32) s33.zero (by decide), g33_4]
  have g34_9 : reg n34 (9 : Fin 32) = op15 := by
    rw [rb34, runBlock_reg _ _ _ (9 : Fin 32) s33.zero (by decide), g33_9]
  have g34_11 : reg n34 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb34, runBlock_reg _ _ _ a1 s33.zero (by decide), g33_11]
  have g34_18 : reg n34 (18 : Fin 32) = out := by
    rw [rb34, runBlock_reg _ _ _ (18 : Fin 32) s33.zero (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by
    rw [rb34, runBlock_reg _ _ _ (19 : Fin 32) s33.zero (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = x20 := by
    rw [rb34, runBlock_reg _ _ _ (20 : Fin 32) s33.zero (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by
    rw [rb34, runBlock_reg _ _ _ (21 : Fin 32) s33.zero (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = x22 := by
    rw [rb34, runBlock_reg _ _ _ (22 : Fin 32) s33.zero (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = x23 := by
    rw [rb34, runBlock_reg _ _ _ (23 : Fin 32) s33.zero (by decide), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = rem := by
    rw [rb34, runBlock_reg _ _ _ (24 : Fin 32) s33.zero (by decide), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by
    rw [rb34, runBlock_reg _ _ _ (25 : Fin 32) s33.zero (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = ol15 := by
    rw [rb34, runBlock_reg _ _ _ (26 : Fin 32) s33.zero (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = L0 := by
    rw [rb34, runBlock_reg _ _ _ (27 : Fin 32) s33.zero (by decide), g33_27]
  have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svTraf4a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_10, g33_11, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g34_10 : reg n34 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svTraf4a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_10, g33_11, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m34]; exact w33_40
  have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m34]; exact w33_64
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m34]; exact w33_7c
  have w34_25c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m34]; exact w33_25c
  have w34_260 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m34]; exact w33_260
  have w34_264 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m34]; exact w33_264
  have w34_268 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m34]; exact w33_268
  have w34_3e0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m34]; exact w33_3e0
  have w34_3e4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m34]; exact w33_3e4
  have w34_3e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m34]; exact w33_3e8
  have w34_3ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m34]; exact w33_3ec
  have w34_400 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_400
  have w34_404 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_404
  have w34_408 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_408
  have w34_40c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_40c
  have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_420
  have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_424
  have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m34]; exact w33_428
  have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m34]; exact w33_42c
  have b34_424 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m34]; exact b33_424
  have b34_425 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m34]; exact b33_425
  have b34_426 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m34]; exact b33_426
  have b34_427 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m34]; exact b33_427
  clear b33_427 b33_426 b33_425 b33_424 w33_42c w33_428 w33_424 w33_420 w33_40c w33_408 w33_404 w33_400 w33_3ec w33_3e8 w33_3e4 w33_3e0 w33_268 w33_264 w33_260 w33_25c w33_7c w33_64 w33_40 g33_2 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 V33 E33 fR33 t33 fr33 K33 rk33 sp33 s33 c33
  -- 0xF4E: branch, not taken
  obtain ⟨n35, d35, u35⟩ := s34.notTaken E34.self 0xF52 sv_at_f4e
    (by decide) (by rw [g34_10, s34.zero]; decide)
  have s35 : St n35.mem SV n35 0xF52 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans (.single d35)
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u35.regs, g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = op15 := by rw [u35.regs, g34_9]
  have g35_10 : reg n35 a0 = BitVec.ofNat 32 0x0 := by rw [u35.regs, g34_10]
  have g35_11 : reg n35 a1 = BitVec.ofNat 32 0x0 := by rw [u35.regs, g34_11]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = x20 := by rw [u35.regs, g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [u35.regs, g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [u35.regs, g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = x23 := by rw [u35.regs, g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = rem := by rw [u35.regs, g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u35.regs, g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = ol15 := by rw [u35.regs, g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = L0 := by rw [u35.regs, g34_27]
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m35]; exact w34_40
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m35]; exact w34_64
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m35]; exact w34_7c
  have w35_25c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m35]; exact w34_25c
  have w35_260 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m35]; exact w34_260
  have w35_264 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m35]; exact w34_264
  have w35_268 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m35]; exact w34_268
  have w35_3e0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m35]; exact w34_3e0
  have w35_3e4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m35]; exact w34_3e4
  have w35_3e8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m35]; exact w34_3e8
  have w35_3ec : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m35]; exact w34_3ec
  have w35_400 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_400
  have w35_404 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_404
  have w35_408 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_408
  have w35_40c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_40c
  have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_420
  have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_424
  have w35_428 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m35]; exact w34_428
  have w35_42c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m35]; exact w34_42c
  have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m35]; exact b34_424
  have b35_425 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m35]; exact b34_425
  have b35_426 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m35]; exact b34_426
  have b35_427 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m35]; exact b34_427
  clear b34_427 b34_426 b34_425 b34_424 w34_42c w34_428 w34_424 w34_420 w34_40c w34_408 w34_404 w34_400 w34_3ec w34_3e8 w34_3e4 w34_3e0 w34_268 w34_264 w34_260 w34_25c w34_7c w34_64 w34_40 g34_10 g34_8 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_11 g34_9 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34 g33_11 g33_10 a1_33 a0_33
  -- 0xF52
  obtain ⟨n36, c36, u36⟩ := s35.block svTraf52 E35.self svTraf52_end
    ⟨trivial, trivial, trivial⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have s36 : St n36.mem SV n36 0xF58 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have rb36 : ∀ q, reg n36 q = (runBlock svTraf52 (n35.mem, reg n35)).2 q := fun q => by rw [u36.regs]
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans c36
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by
    rw [rb36, runBlock_reg _ _ _ sp s35.zero (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb36, runBlock_reg _ _ _ (3 : Fin 32) s35.zero (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb36, runBlock_reg _ _ _ (4 : Fin 32) s35.zero (by decide), g35_4]
  have g36_9 : reg n36 (9 : Fin 32) = op15 := by
    rw [rb36, runBlock_reg _ _ _ (9 : Fin 32) s35.zero (by decide), g35_9]
  have g36_11 : reg n36 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb36, runBlock_reg _ _ _ a1 s35.zero (by decide), g35_11]
  have g36_18 : reg n36 (18 : Fin 32) = out := by
    rw [rb36, runBlock_reg _ _ _ (18 : Fin 32) s35.zero (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by
    rw [rb36, runBlock_reg _ _ _ (19 : Fin 32) s35.zero (by decide), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = x20 := by
    rw [rb36, runBlock_reg _ _ _ (20 : Fin 32) s35.zero (by decide), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = x21 := by
    rw [rb36, runBlock_reg _ _ _ (21 : Fin 32) s35.zero (by decide), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = x22 := by
    rw [rb36, runBlock_reg _ _ _ (22 : Fin 32) s35.zero (by decide), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = x23 := by
    rw [rb36, runBlock_reg _ _ _ (23 : Fin 32) s35.zero (by decide), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = rem := by
    rw [rb36, runBlock_reg _ _ _ (24 : Fin 32) s35.zero (by decide), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by
    rw [rb36, runBlock_reg _ _ _ (25 : Fin 32) s35.zero (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = ol15 := by
    rw [rb36, runBlock_reg _ _ _ (26 : Fin 32) s35.zero (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = L0 := by
    rw [rb36, runBlock_reg _ _ _ (27 : Fin 32) s35.zero (by decide), g35_27]
  have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb36]; simp +decide only [runBlock, BInstr.run, svTraf52, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_10, g35_11, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, s35.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g36_10 : reg n36 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb36]; simp +decide only [runBlock, BInstr.run, svTraf52, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_10, g35_11, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, s35.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m36]; exact w35_40
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m36]; exact w35_64
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m36]; exact w35_7c
  have w36_25c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m36]; exact w35_25c
  have w36_260 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m36]; exact w35_260
  have w36_264 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m36]; exact w35_264
  have w36_268 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m36]; exact w35_268
  have w36_3e0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m36]; exact w35_3e0
  have w36_3e4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m36]; exact w35_3e4
  have w36_3e8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m36]; exact w35_3e8
  have w36_3ec : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m36]; exact w35_3ec
  have w36_400 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m36]; exact w35_400
  have w36_404 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m36]; exact w35_404
  have w36_408 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m36]; exact w35_408
  have w36_40c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m36]; exact w35_40c
  have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m36]; exact w35_420
  have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m36]; exact w35_424
  have w36_428 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m36]; exact w35_428
  have w36_42c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m36]; exact w35_42c
  have b36_424 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m36]; exact b35_424
  have b36_425 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m36]; exact b35_425
  have b36_426 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m36]; exact b35_426
  have b36_427 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m36]; exact b35_427
  clear b35_427 b35_426 b35_425 b35_424 w35_42c w35_428 w35_424 w35_420 w35_40c w35_408 w35_404 w35_400 w35_3ec w35_3e8 w35_3e4 w35_3e0 w35_268 w35_264 w35_260 w35_25c w35_7c w35_64 w35_40 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_11 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
  -- 0xF58: branch, not taken
  obtain ⟨n37, d37, u37⟩ := s36.notTaken E36.self 0xF5C sv_at_f58
    (by decide) (by rw [g36_10, s36.zero]; decide)
  have s37 : St n37.mem SV n37 0xF5C (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans (.single d37)
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u37.regs, g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = op15 := by rw [u37.regs, g36_9]
  have g37_10 : reg n37 a0 = BitVec.ofNat 32 0x0 := by rw [u37.regs, g36_10]
  have g37_11 : reg n37 a1 = BitVec.ofNat 32 0x0 := by rw [u37.regs, g36_11]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = x20 := by rw [u37.regs, g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [u37.regs, g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = x22 := by rw [u37.regs, g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = x23 := by rw [u37.regs, g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = rem := by rw [u37.regs, g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [u37.regs, g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = ol15 := by rw [u37.regs, g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = L0 := by rw [u37.regs, g36_27]
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1)] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = p0 := by rw [m37]; exact w36_40
  have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m37]; exact w36_64
  have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m37]; exact w36_7c
  have w37_25c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m37]; exact w36_25c
  have w37_260 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m37]; exact w36_260
  have w37_264 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (cp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m37]; exact w36_264
  have w37_268 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rem) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m37]; exact w36_268
  have w37_3e0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = (cp) + BitVec.ofNat 32 tl6.header := by rw [m37]; exact w36_3e0
  have w37_3e4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl6.len := by rw [m37]; exact w36_3e4
  have w37_3e8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m37]; exact w36_3e8
  have w37_3ec : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl6.len) - BitVec.ofNat 32 (to15.header + to15.len)) - BitVec.ofNat 32 (tl20.header + tl20.len) := by rw [m37]; exact w36_3ec
  have w37_400 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m37]; exact w36_400
  have w37_404 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 tl20.len := by rw [m37]; exact w36_404
  have w37_408 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m37]; exact w36_408
  have w37_40c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 tl20.len := by rw [m37]; exact w36_40c
  have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m37]; exact w36_420
  have w37_424 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl20.len := by rw [m37]; exact w36_424
  have w37_428 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((cp) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (to15.header + to15.len)) + BitVec.ofNat 32 tl20.header := by rw [m37]; exact w36_428
  have w37_42c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl20.len := by rw [m37]; exact w36_42c
  have b37_424 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl20.len).extractLsb' 0 8 := by rw [m37]; exact b36_424
  have b37_425 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl20.len).extractLsb' 8 8 := by rw [m37]; exact b36_425
  have b37_426 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl20.len).extractLsb' 16 8 := by rw [m37]; exact b36_426
  have b37_427 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl20.len).extractLsb' 24 8 := by rw [m37]; exact b36_427
  clear b36_427 b36_426 b36_425 b36_424 w36_42c w36_428 w36_424 w36_420 w36_40c w36_408 w36_404 w36_400 w36_3ec w36_3e8 w36_3e4 w36_3e0 w36_268 w36_264 w36_260 w36_25c w36_7c w36_64 w36_40 g36_10 g36_8 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_11 g36_9 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 rb36 s36 m36 u36 c36
  exact .inr ⟨hle, tl6, hr6, op15, ol15, hr15, to15, ht15, tl20, hr20, hrest0, hr33, n37, t37, s37, E37, V37, fR37, g37_2, g37_3, g37_4, g37_18, g37_19, g37_20, g37_21, g37_22, g37_23, g37_24, g37_25, g37_26, g37_27, w37_64, w37_7c, w37_25c, w37_260, w37_264, w37_268, w37_408, w37_40c, keep_kk37.mono (by decide)⟩

end C3.RV32.Sv
