import C3BootProofs.Proofs.SvCongr

/-!
# `sigstore::verify`: the `tbsCertificate`

From the call to `Der::element` for the `tbsCertificate` at 0x9A to the serial number at 0x158: the certificate's three parts, the empty rest, and the version, which must be `[0] EXPLICIT INTEGER 2`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL2ae : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x370, .aluImm .add a2 x0 0x30]
theorem svL2ae_end : blockEnd sigstoreVerifyCode 0xAE svL2ae = some 0xB6 := by
  simp only [svL2ae]
  rw [blockEnd, sv_at_ae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL2cc : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x370]
theorem svL2cc_end : blockEnd sigstoreVerifyCode 0xCC svL2cc = some 0xD0 := by
  simp only [svL2cc]
  rw [blockEnd, sv_at_cc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_ce]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL2ec : List BInstr :=
  [.aluImm .add a0 sp 0x280]
theorem svL2ec_end : blockEnd sigstoreVerifyCode 0xEC svL2ec = some 0xEE := by
  simp only [svL2ec]
  rw [blockEnd, sv_at_ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL2fa : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x27C, .aluImm .add a2 x0 0xA0]
theorem svL2fa_end : blockEnd sigstoreVerifyCode 0xFA svL2fa = some 0x102 := by
  simp only [svL2fa]
  rw [blockEnd, sv_at_fa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_fc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_fe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL2150 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x15]
theorem svL2150_end : blockEnd sigstoreVerifyCode 0x150 svL2150 = some 0x152 := by
  simp only [svL2150]
  rw [blockEnd, sv_at_150]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL211a : List BInstr :=
  [.alu .add (25 : Fin 32) x0 (8 : Fin 32)]
theorem svL211a_end : blockEnd sigstoreVerifyCode 0x11A svL211a = some 0x11C := by
  simp only [svL211a]
  rw [blockEnd, sv_at_11a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL211e : List BInstr :=
  [.aluImm .add a2 sp 0x200]
theorem svL211e_end : blockEnd sigstoreVerifyCode 0x11E svL211e = some 0x120 := by
  simp only [svL211e]
  rw [blockEnd, sv_at_11e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL2128 : List BInstr :=
  [.aluImm .add a0 sp 0x25C, .aluImm .add a1 x0 0x2]
theorem svL2128_end : blockEnd sigstoreVerifyCode 0x128 svL2128 = some 0x12C := by
  simp only [svL2128]
  rw [blockEnd, sv_at_128]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_12a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL2134 : List BInstr :=
  [.aluImm .and a0 a0 0x1, .alu .add (8 : Fin 32) x0 a1]
theorem svL2134_end : blockEnd sigstoreVerifyCode 0x134 svL2134 = some 0x138 := by
  simp only [svL2134]
  rw [blockEnd, sv_at_134]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_136]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL213c : List BInstr :=
  [.aluImm .and a0 (8 : Fin 32) 0x1, .aluImm .add (8 : Fin 32) x0 0x15]
theorem svL213c_end : blockEnd sigstoreVerifyCode 0x13C svL213c = some 0x142 := by
  simp only [svL213c]
  rw [blockEnd, sv_at_13c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_140]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL214c : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x1]
theorem svL214c_end : blockEnd sigstoreVerifyCode 0x14C svL214c = some 0x14E := by
  simp only [svL214c]
  rw [blockEnd, sv_at_14c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL2154 : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x27C]
theorem svL2154_end : blockEnd sigstoreVerifyCode 0x154 svL2154 = some 0x158 := by
  simp only [svL2154]
  rw [blockEnd, sv_at_154]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_156]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_l2 {B out bp rootp dg lp ll cp cl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x9A (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80)
    (g0_11 : reg n0 a1 = B + 0x21A0 + BitVec.ofNat 32 0x370)
    (g0_12 : reg n0 a2 = BitVec.ofNat 32 0x30)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = dg)
    (g0_21 : reg n0 (21 : Fin 32) = rootp)
    (g0_22 : reg n0 (22 : Fin 32) = ll)
    (g0_26 : reg n0 (26 : Fin 32) = lp)
    (w0_378 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = cp)
    (w0_37c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = cl)
    (cc_in : SvIn B (cp) (cl).toNat) :
    (¬ (∃ tl1, derElement 0x30 (memBytes M0 (cp) (cl).toNat) = .ok tl1 ∧ ∃ tl8, derElement 0x30 (memBytes M0 ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)).toNat) = .ok tl8 ∧ ∃ tl16, derElement 3 (memBytes M0 (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) = .ok tl16 ∧ ∃ bp16 bl16, derBitsOf (memBytes M0 (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (.ok tl16) = .ok (bp16, bl16) ∧ ((((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) = 0) ∧ ∃ tl28, derOptRes 0xA0 (memBytes M0 ((cp) + BitVec.ofNat 32 tl1.header) (BitVec.ofNat 32 tl1.len).toNat) = some (.ok tl28) ∧ derIntIsOf M0 (memBytes M0 (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) (BitVec.ofNat 32 tl28.len).toNat) (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) (derElement 2 (memBytes M0 (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) (BitVec.ofNat 32 tl28.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true ∧ ∃ te41, derElement 2 (memBytes M0 (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) (BitVec.ofNat 32 tl28.len).toNat) = .ok te41 ∧ ((BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl1, derElement 0x30 (memBytes M0 (cp) (cl).toNat) = .ok tl1 ∧
    ∃ tl8, derElement 0x30 (memBytes M0 ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)).toNat) = .ok tl8 ∧
    ∃ tl16, derElement 3 (memBytes M0 (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) = .ok tl16 ∧
    ∃ bp16 bl16, derBitsOf (memBytes M0 (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (.ok tl16) = .ok (bp16, bl16) ∧
    ((((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) = 0) ∧
    ∃ tl28, derOptRes 0xA0 (memBytes M0 ((cp) + BitVec.ofNat 32 tl1.header) (BitVec.ofNat 32 tl1.len).toNat) = some (.ok tl28) ∧
    derIntIsOf M0 (memBytes M0 (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) (BitVec.ofNat 32 tl28.len).toNat) (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) (derElement 2 (memBytes M0 (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) (BitVec.ofNat 32 tl28.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true ∧
    ∃ te41, derElement 2 (memBytes M0 (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) (BitVec.ofNat 32 tl28.len).toNat) = .ok te41 ∧
    ((BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x158 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x15 ∧
        reg n' (9 : Fin 32) = cp ∧
        reg n' a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 ∧
        reg n' a1 = B + 0x21A0 + BitVec.ofNat 32 0x27C ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (23 : Fin 32) = bp16 ∧
        reg n' (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header ∧
        reg n' (25 : Fin 32) = bl16 ∧
        reg n' (26 : Fin 32) = lp ∧
        reg n' (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) ∧
        SvKeepL B n0.mem n'.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x9A: sv_elemF
  obtain ⟨n1, c1, s1, rk1, K1, Ok1, Er1, fr1⟩ := sv_elemF (oc := 0x80) (dc := 0x370) (tag := 0x30)
    F E0 s0 sv_at_9a sv_at_9e (by decide) (by decide) g0_10 g0_11 g0_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w0_378 w0_37c
  have t1 : Steps n0 n1 := t0.trans c1
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.keepL K1 (by decide)
  rw [sv_mb fR0 cc_in] at Ok1 Er1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [rk1 sp (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk1 (3 : Fin 32) (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk1 (4 : Fin 32) (by decide) (by decide), g0_4]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [rk1 a0 (by decide) (by decide), g0_10]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [rk1 (18 : Fin 32) (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [rk1 (19 : Fin 32) (by decide) (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = dg := by rw [rk1 (20 : Fin 32) (by decide) (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = rootp := by rw [rk1 (21 : Fin 32) (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = ll := by rw [rk1 (22 : Fin 32) (by decide) (by decide), g0_22]
  have g1_26 : reg n1 (26 : Fin 32) = lp := by rw [rk1 (26 : Fin 32) (by decide) (by decide), g0_26]
  obtain ⟨r1, hr1⟩ : ∃ r, derElement 0x30 (memBytes M0 (cp) (cl).toNat) = r := ⟨_, rfl⟩
  rcases r1 with er1 | tl1
  · obtain ⟨zhr1, -⟩ := Er1 er1 hr1
    have keep_kk1 : SvKeepL B n0.mem n1.mem [(0x80, 0x11), (0x378, 0x8)] := (SvKeepL.refl : SvKeepL B n0.mem n0.mem []).trans K1
    have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := zhr1
    -- 0xA2: lw
    obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_a2 (off' := 0xA4) (by decide)
      (by rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s2 : St n2.mem SV n2 0xA4 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
    have m2 : n2.mem = n1.mem := u2.mem
    have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
    have t2 : Steps n0 n2 := t1.trans (.single d2)
    have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
    have E2 : SvCode n2.mem := E1.fr F fr2
    have V2 : SvSaves B n2.mem v := V1.same m2
    have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
    have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
    have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
    have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_10]
    have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
    have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
    have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
    have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
    have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
    have g2_26 : reg n2 (26 : Fin 32) = lp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
    have g2_24 : reg n2 (24 : Fin 32) = 0 := by
      rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w1_80]
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x80, 0x11), (0x378, 0x8)] := by rw [m2]; exact keep_kk1
    clear keep_kk1
    have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m2]; exact w1_80
    clear w1_80 zhr1
    -- 0xA4: branch, taken
    obtain ⟨n3, d3, u3⟩ := s2.taken E2.self 0x7A0 sv_at_a4
      (by decide) (by rw [g2_24, s2.zero]; rfl)
    have s3 : St n3.mem SV n3 0x7A0 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
    have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [u3.regs, g2_10]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, g2_20]
    have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, g2_22]
    have g3_24 : reg n3 (24 : Fin 32) = 0 := by rw [u3.regs, g2_24]
    have g3_26 : reg n3 (26 : Fin 32) = lp := by rw [u3.regs, g2_26]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x80, 0x11), (0x378, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m3]; exact w2_80
    clear w2_80 g2_24 g2_26 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
    -- 0x7A0: lbu
    obtain ⟨n4, d4, u4⟩ := s3.lbu E3.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s4 : St n4.mem SV n4 0x7A4 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
    have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_10]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
    have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
    have g4_24 : reg n4 (24 : Fin 32) = 0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_24]
    have g4_26 : reg n4 (26 : Fin 32) = lp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x80, 0x11), (0x378, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m4]; exact w3_80
    clear w3_80 g3_26 g3_24 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    exact .inl ⟨(fun ⟨tl1', h0', _⟩ => by rw [hr1] at h0'; cases h0'), sv_fail F E4 s4 t4 (fun x hx => (fR4 x hx).trans (fM x hx).symm) V4 hret g4_2 g4_18 hO g4_3 g4_4⟩
  obtain ⟨o0_1, o4_1, o8_1, o12_1, o16_1, d8_1, d12_1⟩ := Ok1 tl1 hr1
  have keep_kk1 : SvKeepL B n0.mem n1.mem [(0x80, 0x11), (0x378, 0x8)] := (SvKeepL.refl : SvKeepL B n0.mem n0.mem []).trans K1
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (cp) + BitVec.ofNat 32 tl1.header := o0_1
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := o4_1
  have w1_88 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = cp := o8_1
  have w1_8c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl1.header + tl1.len) := o12_1
  have w1_378 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := d8_1
  have w1_37c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := d12_1
  have b1_90 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl1.tag := o16_1
  -- 0xA2: lw
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_a2 (off' := 0xA4) (by decide)
    (by rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s2 : St n2.mem SV n2 0xA4 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_26 : reg n2 (26 : Fin 32) = lp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_24 : reg n2 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w1_80]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x80, 0x11), (0x378, 0x8)] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m2]; exact w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m2]; exact w1_84
  have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = cp := by rw [m2]; exact w1_88
  have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_8c
  have w2_378 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_378
  have w2_37c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_37c
  have b2_90 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl1.tag := by rw [m2]; exact b1_90
  clear b1_90 w1_37c w1_378 w1_8c w1_88 w1_84 w1_80 d12_1 d8_1 o16_1 o12_1 o8_1 o4_1 o0_1 g1_26 g1_22 g1_21 g1_20 g1_19 g1_18 g1_10 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 Er1 Ok1 K1 rk1 s1 c1 g0_4 g0_3 fR0 t0
  -- 0xA4: branch, not taken
  obtain ⟨n3, d3, u3⟩ := s2.notTaken E2.self 0xA8 sv_at_a4
    (by decide) (by rw [g2_24, s2.zero]; exact br_beq_f (cc_in.ok_ne hr1))
  have s3 : St n3.mem SV n3 0xA8 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [u3.regs, g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, g2_22]
  have g3_24 : reg n3 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u3.regs, g2_24]
  have g3_26 : reg n3 (26 : Fin 32) = lp := by rw [u3.regs, g2_26]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x80, 0x11), (0x378, 0x8)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m3]; exact w2_84
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = cp := by rw [m3]; exact w2_88
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_8c
  have w3_378 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_378
  have w3_37c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_37c
  have b3_90 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl1.tag := by rw [m3]; exact b2_90
  clear b2_90 w2_37c w2_378 w2_8c w2_88 w2_84 w2_80 g2_24 g2_26 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0xA8: lw
  obtain ⟨n4, d4, u4⟩ := s3.lw E3.self sv_at_a8 (off' := 0xAA) (by decide)
    (by rw [g3_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s4 : St n4.mem SV n4 0xAA (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_10]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
  have g4_24 : reg n4 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u4.regs, upd_ne (by decide) (by decide), g3_24]
  have g4_26 : reg n4 (26 : Fin 32) = lp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
  have g4_25 : reg n4 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, w3_84]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x80, 0x11), (0x378, 0x8)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m4]; exact w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = cp := by rw [m4]; exact w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_8c
  have w4_378 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_378
  have w4_37c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_37c
  have b4_90 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl1.tag := by rw [m4]; exact b3_90
  clear b3_90 w3_37c w3_378 w3_8c w3_88 w3_84 w3_80 g3_26 g3_24 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0xAA: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_aa (off' := 0xAC) (by decide)
    (by rw [g4_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0xAC (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = dg := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = rootp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = ll := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
  have g5_24 : reg n5 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = lp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_9 : reg n5 (9 : Fin 32) = cp := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr, w4_88]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x80, 0x11), (0x378, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m5]; exact w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = cp := by rw [m5]; exact w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_8c
  have w5_378 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_378
  have w5_37c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_37c
  have b5_90 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl1.tag := by rw [m5]; exact b4_90
  clear b4_90 w4_37c w4_378 w4_8c w4_88 w4_84 w4_80 g4_25 g4_26 g4_24 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0xAC: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_ac (off' := 0xAE) (by decide)
    (by rw [g5_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0xAE (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = cp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_24 : reg n6 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = lp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr, w5_8c]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x80, 0x11), (0x378, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m6]; exact w5_84
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = cp := by rw [m6]; exact w5_88
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m6]; exact w5_8c
  have w6_378 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m6]; exact w5_378
  have w6_37c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m6]; exact w5_37c
  have b6_90 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl1.tag := by rw [m6]; exact b5_90
  clear b5_90 w5_37c w5_378 w5_8c w5_88 w5_84 w5_80 g5_9 g5_26 g5_25 g5_24 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0xAE
  obtain ⟨n7, c7, u7⟩ := s6.block svL2ae E6.self svL2ae_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0xB6 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svL2ae (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_9 : reg n7 (9 : Fin 32) = cp := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
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
  have g7_24 : reg n7 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = lp := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svL2ae, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_9, g6_10, g6_18, g6_19, g6_20, g6_21, g6_22, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g7_11 : reg n7 a1 = B + 0x21A0 + BitVec.ofNat 32 0x370 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svL2ae, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_9, g6_10, g6_18, g6_19, g6_20, g6_21, g6_22, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g7_12 : reg n7 a2 = BitVec.ofNat 32 0x30 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svL2ae, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_9, g6_10, g6_18, g6_19, g6_20, g6_21, g6_22, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x80, 0x11), (0x378, 0x8)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m7]; exact w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m7]; exact w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = cp := by rw [m7]; exact w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_8c
  have w7_378 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_378
  have w7_37c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_37c
  have b7_90 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl1.tag := by rw [m7]; exact b6_90
  clear b6_90 w6_37c w6_378 w6_8c w6_88 w6_84 w6_80 g6_27 g6_26 g6_25 g6_24 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0xB6: sv_elemF
  obtain ⟨n8, c8, s8, rk8, K8, Ok8, Er8, fr8⟩ := sv_elemF (oc := 0x80) (dc := 0x370) (tag := 0x30)
    F E7 s7 sv_at_b6 sv_at_ba (by decide) (by decide) g7_10 g7_11 g7_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w7_378 w7_37c
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keepL K8 (by decide)
  rw [sv_mb fR7 (cc_in.restW hr1)] at Ok8 Er8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rk8 sp (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk8 (3 : Fin 32) (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk8 (4 : Fin 32) (by decide) (by decide), g7_4]
  have g8_9 : reg n8 (9 : Fin 32) = cp := by rw [rk8 (9 : Fin 32) (by decide) (by decide), g7_9]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [rk8 a0 (by decide) (by decide), g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rk8 (18 : Fin 32) (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rk8 (19 : Fin 32) (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [rk8 (20 : Fin 32) (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [rk8 (21 : Fin 32) (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [rk8 (22 : Fin 32) (by decide) (by decide), g7_22]
  have g8_24 : reg n8 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rk8 (24 : Fin 32) (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rk8 (25 : Fin 32) (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = lp := by rw [rk8 (26 : Fin 32) (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rk8 (27 : Fin 32) (by decide) (by decide), g7_27]
  obtain ⟨r8, hr8⟩ : ∃ r, derElement 0x30 (memBytes M0 ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)).toNat) = r := ⟨_, rfl⟩
  rcases r8 with er8 | tl8
  · obtain ⟨zhr8, -⟩ := Er8 er8 hr8
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8)] := keep_kk7.trans K8
    clear keep_kk7
    have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := zhr8
    clear b7_90 w7_37c w7_378 w7_8c w7_88 w7_84 w7_80 g7_12 g7_11 g7_10 g7_27 g7_26 g7_25 g7_24 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
    -- 0xBE: lw
    obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_be (off' := 0xC0) (by decide)
      (by rw [g8_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s9 : St n9.mem SV n9 0xC0 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
    have g9_9 : reg n9 (9 : Fin 32) = cp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [u9.regs, upd_ne (by decide) (by decide), g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
    have g9_24 : reg n9 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = lp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
    have g9_10 : reg n9 a0 = 0 := by
      rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g8_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w8_80]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m9]; exact w8_80
    clear w8_80 zhr8
    -- 0xC0: branch, taken
    obtain ⟨n10, d10, u10⟩ := s9.taken E9.self 0x7A0 sv_at_c0
      (by decide) (by rw [g9_10, s9.zero]; rfl)
    have s10 : St n10.mem SV n10 0x7A0 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
    have g10_9 : reg n10 (9 : Fin 32) = cp := by rw [u10.regs, g9_9]
    have g10_10 : reg n10 a0 = 0 := by rw [u10.regs, g9_10]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = dg := by rw [u10.regs, g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = rootp := by rw [u10.regs, g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = ll := by rw [u10.regs, g9_22]
    have g10_24 : reg n10 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u10.regs, g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u10.regs, g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = lp := by rw [u10.regs, g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u10.regs, g9_27]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m10]; exact w9_80
    clear w9_80 g9_10 g9_27 g9_26 g9_25 g9_24 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
    -- 0x7A0: lbu
    obtain ⟨n11, d11, u11⟩ := s10.lbu E10.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s11 : St n11.mem SV n11 0x7A4 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
    have g11_9 : reg n11 (9 : Fin 32) = cp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
    have g11_10 : reg n11 a0 = 0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
    have g11_24 : reg n11 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = lp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m11]; exact w10_80
    clear w10_80 g10_27 g10_26 g10_25 g10_24 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'), sv_fail F E11 s11 t11 (fun x hx => (fR11 x hx).trans (fM x hx).symm) V11 hret g11_2 g11_18 hO g11_3 g11_4⟩
  obtain ⟨o0_8, o4_8, o8_8, o12_8, o16_8, d8_8, d12_8⟩ := Ok8 tl8 hr8
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8)] := keep_kk7.trans K8
  clear keep_kk7
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := o0_8
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := o4_8
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := o8_8
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := o12_8
  have w8_378 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := d8_8
  have w8_37c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := d12_8
  have b8_90 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := o16_8
  clear b7_90 w7_37c w7_378 w7_8c w7_88 w7_84 w7_80 g7_12 g7_11 g7_10 g7_27 g7_26 g7_25 g7_24 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0xBE: lw
  obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_be (off' := 0xC0) (by decide)
    (by rw [g8_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s9 : St n9.mem SV n9 0xC0 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
  have g9_9 : reg n9 (9 : Fin 32) = cp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [u9.regs, upd_ne (by decide) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
  have g9_24 : reg n9 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = lp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
  have g9_10 : reg n9 a0 = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g8_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w8_80]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m9]; exact w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := by rw [m9]; exact w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m9]; exact w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m9]; exact w8_8c
  have w9_378 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m9]; exact w8_378
  have w9_37c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m9]; exact w8_37c
  have b9_90 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m9]; exact b8_90
  clear b8_90 w8_37c w8_378 w8_8c w8_88 w8_84 w8_80 d12_8 d8_8 o16_8 o12_8 o8_8 o4_8 o0_8 g8_27 g8_26 g8_25 g8_24 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 Er8 Ok8 K8 rk8 s8 c8
  -- 0xC0: branch, not taken
  obtain ⟨n10, d10, u10⟩ := s9.notTaken E9.self 0xC4 sv_at_c0
    (by decide) (by rw [g9_10, s9.zero]; exact br_beq_f ((cc_in.restW hr1).ok_ne hr8))
  have s10 : St n10.mem SV n10 0xC4 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
  have g10_9 : reg n10 (9 : Fin 32) = cp := by rw [u10.regs, g9_9]
  have g10_10 : reg n10 a0 = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [u10.regs, g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = dg := by rw [u10.regs, g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = rootp := by rw [u10.regs, g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = ll := by rw [u10.regs, g9_22]
  have g10_24 : reg n10 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u10.regs, g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u10.regs, g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = lp := by rw [u10.regs, g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u10.regs, g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := by rw [m10]; exact w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m10]; exact w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m10]; exact w9_8c
  have w10_378 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m10]; exact w9_378
  have w10_37c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m10]; exact w9_37c
  have b10_90 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m10]; exact b9_90
  clear b9_90 w9_37c w9_378 w9_8c w9_88 w9_84 w9_80 g9_10 g9_27 g9_26 g9_25 g9_24 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0xC4: lw
  obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_c4 (off' := 0xC6) (by decide)
    (by rw [g10_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s11 : St n11.mem SV n11 0xC6 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
  have g11_9 : reg n11 (9 : Fin 32) = cp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
  have g11_24 : reg n11 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = lp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
  have g11_10 : reg n11 a0 = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g10_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr, w10_88]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m11]; exact w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := by rw [m11]; exact w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m11]; exact w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m11]; exact w10_8c
  have w11_378 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m11]; exact w10_378
  have w11_37c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m11]; exact w10_37c
  have b11_90 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m11]; exact b10_90
  clear b10_90 w10_37c w10_378 w10_8c w10_88 w10_84 w10_80 g10_27 g10_26 g10_25 g10_24 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0xC6: sw
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sw F E11 s11 sv_at_c6 (off' := 0xC8) (c := 0x7C)
    (by decide) (by rw [g11_2]; sv_addr) (by decide) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_9 : reg n12 (9 : Fin 32) = cp := by rw [rg12 (9 : Fin 32), g11_9]
  have g12_10 : reg n12 a0 = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg12 a0, g11_10]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = dg := by rw [rg12 (20 : Fin 32), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = rootp := by rw [rg12 (21 : Fin 32), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = ll := by rw [rg12 (22 : Fin 32), g11_22]
  have g12_24 : reg n12 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg12 (25 : Fin 32), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = lp := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg12 (27 : Fin 32), g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := (K12.w32 (by decide) (by decide)).trans w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := (K12.w32 (by decide) (by decide)).trans w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K12.w32 (by decide) (by decide)).trans w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K12.w32 (by decide) (by decide)).trans w11_8c
  have w12_378 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K12.w32 (by decide) (by decide)).trans w11_378
  have w12_37c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K12.w32 (by decide) (by decide)).trans w11_37c
  have b12_90 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K12.b8 (by decide) (by decide)).trans b11_90
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [W12, g11_10]
  clear b11_90 w11_37c w11_378 w11_8c w11_88 w11_84 w11_80 g11_10 g11_27 g11_26 g11_25 g11_24 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0xC8: lw
  obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_c8 (off' := 0xCA) (by decide)
    (by rw [g12_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s13 : St n13.mem SV n13 0xCA (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_9 : reg n13 (9 : Fin 32) = cp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = dg := by rw [u13.regs, upd_ne (by decide) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = rootp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = ll := by rw [u13.regs, upd_ne (by decide) (by decide), g12_22]
  have g13_24 : reg n13 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = lp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
  have g13_10 : reg n13 a0 = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr, w12_8c]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m13]; exact w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := by rw [m13]; exact w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m13]; exact w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m13]; exact w12_8c
  have w13_378 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m13]; exact w12_378
  have w13_37c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m13]; exact w12_37c
  have b13_90 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m13]; exact b12_90
  clear w12_7c b12_90 w12_37c w12_378 w12_8c w12_88 w12_84 w12_80 g12_27 g12_26 g12_25 g12_24 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0xCA: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_ca (off' := 0xCC) (c := 0x78)
    (by decide) (by rw [g13_2]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_9 : reg n14 (9 : Fin 32) = cp := by rw [rg14 (9 : Fin 32), g13_9]
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg14 a0, g13_10]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = dg := by rw [rg14 (20 : Fin 32), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = rootp := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = ll := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_24 : reg n14 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = lp := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K14.w32 (by decide) (by decide)).trans w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := (K14.w32 (by decide) (by decide)).trans w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := (K14.w32 (by decide) (by decide)).trans w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K14.w32 (by decide) (by decide)).trans w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K14.w32 (by decide) (by decide)).trans w13_8c
  have w14_378 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K14.w32 (by decide) (by decide)).trans w13_378
  have w14_37c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K14.w32 (by decide) (by decide)).trans w13_37c
  have b14_90 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K14.b8 (by decide) (by decide)).trans b13_90
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [W14, g13_10]
  clear b13_90 w13_37c w13_378 w13_8c w13_88 w13_84 w13_80 w13_7c g13_10 g13_27 g13_26 g13_25 g13_24 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0xCC
  obtain ⟨n15, c15, u15⟩ := s14.block svL2cc E14.self svL2cc_end
    ⟨trivial, trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem SV n15 0xD0 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock svL2cc (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
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
  have g15_9 : reg n15 (9 : Fin 32) = cp := by
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
  have g15_24 : reg n15 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb15, runBlock_reg _ _ _ (25 : Fin 32) s14.zero (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = lp := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb15, runBlock_reg _ _ _ (27 : Fin 32) s14.zero (by decide), g14_27]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svL2cc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_9, g14_10, g14_18, g14_19, g14_20, g14_21, g14_22, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g15_11 : reg n15 a1 = B + 0x21A0 + BitVec.ofNat 32 0x370 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svL2cc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_9, g14_10, g14_18, g14_19, g14_20, g14_21, g14_22, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m15]; exact w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m15]; exact w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m15]; exact w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := by rw [m15]; exact w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m15]; exact w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m15]; exact w14_8c
  have w15_378 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m15]; exact w14_378
  have w15_37c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m15]; exact w14_37c
  have b15_90 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m15]; exact b14_90
  clear w14_78 b14_90 w14_37c w14_378 w14_8c w14_88 w14_84 w14_80 w14_7c g14_27 g14_26 g14_25 g14_24 g14_22 g14_21 g14_20 g14_19 g14_18 g14_10 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0xD0: sv_bitsF
  obtain ⟨n16, c16, s16, sp16, rk16, K16, A16, Ok16, Er16, fr16⟩ := sv_bitsF (oc := 0x80) (dc := 0x370)
    F E15 s15 sv_at_d0 sv_at_d4 (by decide) (by decide) g15_2 g15_10 g15_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w15_378 w15_37c ((cc_in.restW hr1).restW hr8)
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keepL K16 (by decide)
  rw [sv_mb fR15 ((cc_in.restW hr1).restW hr8)] at A16 Ok16 Er16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rk16 sp (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk16 (3 : Fin 32) (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk16 (4 : Fin 32) (by decide) (by decide), g15_4]
  have g16_9 : reg n16 (9 : Fin 32) = cp := by rw [rk16 (9 : Fin 32) (by decide) (by decide), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rk16 (18 : Fin 32) (by decide) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rk16 (19 : Fin 32) (by decide) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = dg := by rw [rk16 (20 : Fin 32) (by decide) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = rootp := by rw [rk16 (21 : Fin 32) (by decide) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = ll := by rw [rk16 (22 : Fin 32) (by decide) (by decide), g15_22]
  have g16_24 : reg n16 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rk16 (24 : Fin 32) (by decide) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rk16 (25 : Fin 32) (by decide) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = lp := by rw [rk16 (26 : Fin 32) (by decide) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rk16 (27 : Fin 32) (by decide) (by decide), g15_27]
  obtain ⟨r16, hr16⟩ : ∃ r, derElement 3 (memBytes M0 (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) = r := ⟨_, rfl⟩
  rcases r16 with er16 | tl16
  · obtain ⟨zhr16, -⟩ := Er16 er16 (by rw [hr16]; rfl)
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := keep_kk15.trans K16
    clear keep_kk15
    have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_78
    have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K16.w32 (by decide) (by decide)).trans w15_7c
    have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K16.w32 (by decide) (by decide)).trans w15_88
    have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_8c
    have b16_90 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K16.b8 (by decide) (by decide)).trans b15_90
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := zhr16
    clear b15_90 w15_37c w15_378 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 g15_11 g15_10 g15_27 g15_26 g15_25 g15_24 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
    -- 0xD8: lw
    obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_d8 (off' := 0xDA) (by decide)
      (by rw [g16_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s17 : St n17.mem SV n17 0xDA (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
    have g17_9 : reg n17 (9 : Fin 32) = cp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_9]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [u17.regs, upd_ne (by decide) (by decide), g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
    have g17_24 : reg n17 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = lp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
    have g17_23 : reg n17 (23 : Fin 32) = 0 := by
      rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g16_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w16_80]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m17]; exact w16_78
    have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m17]; exact w16_7c
    have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m17]; exact w16_80
    have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m17]; exact w16_88
    have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m17]; exact w16_8c
    have b17_90 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m17]; exact b16_90
    clear w16_80 b16_90 w16_8c w16_88 w16_7c w16_78 zhr16
    -- 0xDA: branch, taken
    obtain ⟨n18, d18, u18⟩ := s17.taken E17.self 0x7A0 sv_at_da
      (by decide) (by rw [g17_23, s17.zero]; rfl)
    have s18 : St n18.mem SV n18 0x7A0 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
    have g18_9 : reg n18 (9 : Fin 32) = cp := by rw [u18.regs, g17_9]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
    have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [u18.regs, g17_20]
    have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [u18.regs, g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [u18.regs, g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = 0 := by rw [u18.regs, g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u18.regs, g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u18.regs, g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = lp := by rw [u18.regs, g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u18.regs, g17_27]
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m18]; exact keep_kk17
    clear keep_kk17
    have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m18]; exact w17_78
    have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m18]; exact w17_7c
    have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m18]; exact w17_80
    have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m18]; exact w17_88
    have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m18]; exact w17_8c
    have b18_90 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m18]; exact b17_90
    clear b17_90 w17_8c w17_88 w17_80 w17_7c w17_78 g17_23 g17_27 g17_26 g17_25 g17_24 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
    -- 0x7A0: lbu
    obtain ⟨n19, d19, u19⟩ := s18.lbu E18.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s19 : St n19.mem SV n19 0x7A4 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
    have g19_9 : reg n19 (9 : Fin 32) = cp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = dg := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = rootp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = ll := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = 0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = lp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m19]; exact w18_78
    have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m19]; exact w18_7c
    have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m19]; exact w18_80
    have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m19]; exact w18_88
    have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m19]; exact w18_8c
    have b19_90 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m19]; exact b18_90
    clear b18_90 w18_8c w18_88 w18_80 w18_7c w18_78 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'), sv_fail F E19 s19 t19 (fun x hx => (fR19 x hx).trans (fM x hx).symm) V19 hret g19_2 g19_18 hO g19_3 g19_4⟩
  obtain ⟨r16b, hr16b⟩ : ∃ r, derBitsOf (memBytes M0 (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (.ok tl16) = r := ⟨_, rfl⟩
  rcases r16b with er16b | ⟨bp16, bl16⟩
  · obtain ⟨zhr16b, -⟩ := Er16 er16b (by rw [hr16, hr16b])
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := keep_kk15.trans K16
    clear keep_kk15
    have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_78
    have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K16.w32 (by decide) (by decide)).trans w15_7c
    have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K16.w32 (by decide) (by decide)).trans w15_88
    have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_8c
    have b16_90 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K16.b8 (by decide) (by decide)).trans b15_90
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := zhr16b
    clear b15_90 w15_37c w15_378 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 g15_11 g15_10 g15_27 g15_26 g15_25 g15_24 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
    -- 0xD8: lw
    obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_d8 (off' := 0xDA) (by decide)
      (by rw [g16_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s17 : St n17.mem SV n17 0xDA (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
    have g17_9 : reg n17 (9 : Fin 32) = cp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_9]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [u17.regs, upd_ne (by decide) (by decide), g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
    have g17_24 : reg n17 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = lp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
    have g17_23 : reg n17 (23 : Fin 32) = 0 := by
      rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g16_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w16_80]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m17]; exact w16_78
    have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m17]; exact w16_7c
    have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m17]; exact w16_80
    have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m17]; exact w16_88
    have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m17]; exact w16_8c
    have b17_90 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m17]; exact b16_90
    clear w16_80 b16_90 w16_8c w16_88 w16_7c w16_78 zhr16b
    -- 0xDA: branch, taken
    obtain ⟨n18, d18, u18⟩ := s17.taken E17.self 0x7A0 sv_at_da
      (by decide) (by rw [g17_23, s17.zero]; rfl)
    have s18 : St n18.mem SV n18 0x7A0 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
    have g18_9 : reg n18 (9 : Fin 32) = cp := by rw [u18.regs, g17_9]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
    have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [u18.regs, g17_20]
    have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [u18.regs, g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [u18.regs, g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = 0 := by rw [u18.regs, g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u18.regs, g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u18.regs, g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = lp := by rw [u18.regs, g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u18.regs, g17_27]
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m18]; exact keep_kk17
    clear keep_kk17
    have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m18]; exact w17_78
    have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m18]; exact w17_7c
    have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m18]; exact w17_80
    have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m18]; exact w17_88
    have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m18]; exact w17_8c
    have b18_90 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m18]; exact b17_90
    clear b17_90 w17_8c w17_88 w17_80 w17_7c w17_78 g17_23 g17_27 g17_26 g17_25 g17_24 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
    -- 0x7A0: lbu
    obtain ⟨n19, d19, u19⟩ := s18.lbu E18.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s19 : St n19.mem SV n19 0x7A4 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
    have g19_9 : reg n19 (9 : Fin 32) = cp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = dg := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = rootp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = ll := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = 0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = lp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m19]; exact w18_78
    have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m19]; exact w18_7c
    have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m19]; exact w18_80
    have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m19]; exact w18_88
    have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m19]; exact w18_8c
    have b19_90 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m19]; exact b18_90
    clear b18_90 w18_8c w18_88 w18_80 w18_7c w18_78 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'), sv_fail F E19 s19 t19 (fun x hx => (fR19 x hx).trans (fM x hx).symm) V19 hret g19_2 g19_18 hO g19_3 g19_4⟩
  obtain ⟨p0_16, p4_16⟩ := Ok16 bp16 bl16 (by rw [hr16, hr16b])
  obtain ⟨d8_16, d12_16⟩ := A16 tl16 hr16
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := keep_kk15.trans K16
  clear keep_kk15
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K16.w32 (by decide) (by decide)).trans w15_7c
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K16.w32 (by decide) (by decide)).trans w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_8c
  have b16_90 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K16.b8 (by decide) (by decide)).trans b15_90
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := p0_16
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := p4_16
  have w16_378 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := d8_16
  have w16_37c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := d12_16
  clear b15_90 w15_37c w15_378 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 g15_11 g15_10 g15_27 g15_26 g15_25 g15_24 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  -- 0xD8: lw
  obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_d8 (off' := 0xDA) (by decide)
    (by rw [g16_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s17 : St n17.mem SV n17 0xDA (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
  have g17_9 : reg n17 (9 : Fin 32) = cp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [u17.regs, upd_ne (by decide) (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
  have g17_24 : reg n17 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = lp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
  have g17_23 : reg n17 (23 : Fin 32) = bp16 := by
    rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g16_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w16_80]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m17]; exact w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m17]; exact w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := by rw [m17]; exact w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := by rw [m17]; exact w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m17]; exact w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m17]; exact w16_8c
  have w17_378 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m17]; exact w16_378
  have w17_37c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m17]; exact w16_37c
  have b17_90 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m17]; exact b16_90
  clear w16_37c w16_378 w16_84 w16_80 b16_90 w16_8c w16_88 w16_7c w16_78 d12_16 d8_16 p4_16 p0_16 g16_27 g16_26 g16_25 g16_24 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 Er16 Ok16 A16 K16 rk16 sp16 s16 c16
  -- 0xDA: branch, not taken
  obtain ⟨n18, d18, u18⟩ := s17.notTaken E17.self 0xDE sv_at_da
    (by decide) (by rw [g17_23, s17.zero]; exact br_beq_f ((((cc_in.restW hr1).restW hr8).bitsW hr16 hr16b).pos_ne))
  have s18 : St n18.mem SV n18 0xDE (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
  have g18_9 : reg n18 (9 : Fin 32) = cp := by rw [u18.regs, g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [u18.regs, g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [u18.regs, g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [u18.regs, g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = bp16 := by rw [u18.regs, g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u18.regs, g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u18.regs, g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = lp := by rw [u18.regs, g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u18.regs, g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m18]; exact w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m18]; exact w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := by rw [m18]; exact w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := by rw [m18]; exact w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m18]; exact w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m18]; exact w17_8c
  have w18_378 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m18]; exact w17_378
  have w18_37c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m18]; exact w17_37c
  have b18_90 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m18]; exact b17_90
  clear b17_90 w17_37c w17_378 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 g17_23 g17_27 g17_26 g17_25 g17_24 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0xDE: lw
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_de (off' := 0xE2) (by decide)
    (by rw [g18_2, show B + 0x21A0 + 0x37C = B + 0x21A0 + BitVec.ofNat 32 0x37C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s19 : St n19.mem SV n19 0xE2 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_9 : reg n19 (9 : Fin 32) = cp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = dg := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = rootp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = ll := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = bp16 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = lp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_10 : reg n19 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_2, show B + 0x21A0 + 0x37C = B + 0x21A0 + BitVec.ofNat 32 0x37C by sv_addr, w18_37c]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m19]; exact w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m19]; exact w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := by rw [m19]; exact w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := by rw [m19]; exact w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m19]; exact w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m19]; exact w18_8c
  have w19_378 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m19]; exact w18_378
  have w19_37c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m19]; exact w18_37c
  have b19_90 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m19]; exact b18_90
  clear b18_90 w18_37c w18_378 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  by_cases hz_19 : (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) = 0
  rotate_left
  · -- 0xE2: branch, taken
    obtain ⟨n20, d20, u20⟩ := s19.taken E19.self 0x7A4 sv_at_e2
      (by decide) (by rw [g19_10, s19.zero]; exact br_bne_t hz_19)
    have s20 : St n20.mem SV n20 0x7A4 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
    have t20 : Steps n0 n20 := t19.trans (.single d20)
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.same m20
    have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, g19_4]
    have g20_9 : reg n20 (9 : Fin 32) = cp := by rw [u20.regs, g19_9]
    have g20_10 : reg n20 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [u20.regs, g19_10]
    have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, g19_19]
    have g20_20 : reg n20 (20 : Fin 32) = dg := by rw [u20.regs, g19_20]
    have g20_21 : reg n20 (21 : Fin 32) = rootp := by rw [u20.regs, g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = ll := by rw [u20.regs, g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = bp16 := by rw [u20.regs, g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u20.regs, g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u20.regs, g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = lp := by rw [u20.regs, g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u20.regs, g19_27]
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m20]; exact w19_78
    have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m20]; exact w19_7c
    have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := by rw [m20]; exact w19_80
    have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := by rw [m20]; exact w19_84
    have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m20]; exact w19_88
    have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m20]; exact w19_8c
    have w20_378 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m20]; exact w19_378
    have w20_37c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m20]; exact w19_37c
    have b20_90 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m20]; exact b19_90
    clear b19_90 w19_37c w19_378 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; exact hz_19 h4'), sv_fail F E20 s20 t20 (fun x hx => (fR20 x hx).trans (fM x hx).symm) V20 hret g20_2 g20_18 hO g20_3 g20_4⟩
  -- 0xE2: branch, not taken
  obtain ⟨n20, d20, u20⟩ := s19.notTaken E19.self 0xE6 sv_at_e2
    (by decide) (by rw [g19_10, s19.zero]; exact br_bne_f hz_19)
  have s20 : St n20.mem SV n20 0xE6 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, g19_4]
  have g20_9 : reg n20 (9 : Fin 32) = cp := by rw [u20.regs, g19_9]
  have g20_10 : reg n20 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [u20.regs, g19_10]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = dg := by rw [u20.regs, g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = rootp := by rw [u20.regs, g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = ll := by rw [u20.regs, g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = bp16 := by rw [u20.regs, g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u20.regs, g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u20.regs, g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = lp := by rw [u20.regs, g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u20.regs, g19_27]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m20]; exact w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m20]; exact w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := by rw [m20]; exact w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := by rw [m20]; exact w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m20]; exact w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m20]; exact w19_8c
  have w20_378 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m20]; exact w19_378
  have w20_37c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m20]; exact w19_37c
  have b20_90 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m20]; exact b19_90
  clear b19_90 w19_37c w19_378 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0xE6: lw
  obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_e6 (off' := 0xE8) (by decide)
    (by rw [g20_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s21 : St n21.mem SV n21 0xE8 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
  have g21_9 : reg n21 (9 : Fin 32) = cp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
  have g21_10 : reg n21 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_10]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = dg := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = rootp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = ll := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = bp16 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = lp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
  have g21_8 : reg n21 (8 : Fin 32) = bl16 := by
    rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g20_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, w20_84]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m21]; exact w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m21]; exact w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := by rw [m21]; exact w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := by rw [m21]; exact w20_84
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m21]; exact w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m21]; exact w20_8c
  have w21_378 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m21]; exact w20_378
  have w21_37c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m21]; exact w20_37c
  have b21_90 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m21]; exact b20_90
  clear b20_90 w20_37c w20_378 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
  -- 0xE8: sw
  obtain ⟨n22, d22, s22, fr22, K22, W22, rg22⟩ := sv_sw F E21 s21 sv_at_e8 (off' := 0xEC) (c := 0x27C)
    (by decide) (by rw [g21_2]; sv_addr) (by decide) (by decide)
  have t22 : Steps n0 n22 := t21.trans d22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keep K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [rg22 sp, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg22 (3 : Fin 32), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg22 (4 : Fin 32), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = bl16 := by rw [rg22 (8 : Fin 32), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = cp := by rw [rg22 (9 : Fin 32), g21_9]
  have g22_10 : reg n22 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [rg22 a0, g21_10]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rg22 (18 : Fin 32), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rg22 (19 : Fin 32), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [rg22 (20 : Fin 32), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [rg22 (21 : Fin 32), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [rg22 (22 : Fin 32), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = bp16 := by rw [rg22 (23 : Fin 32), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg22 (24 : Fin 32), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg22 (25 : Fin 32), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = lp := by rw [rg22 (26 : Fin 32), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg22 (27 : Fin 32), g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4)] := keep_kk21.trans K22.toL
  clear keep_kk21
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K22.w32 (by decide) (by decide)).trans w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K22.w32 (by decide) (by decide)).trans w21_7c
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := (K22.w32 (by decide) (by decide)).trans w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := (K22.w32 (by decide) (by decide)).trans w21_84
  have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K22.w32 (by decide) (by decide)).trans w21_88
  have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K22.w32 (by decide) (by decide)).trans w21_8c
  have w22_378 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K22.w32 (by decide) (by decide)).trans w21_378
  have w22_37c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K22.w32 (by decide) (by decide)).trans w21_37c
  have b22_90 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K22.b8 (by decide) (by decide)).trans b21_90
  have w22_27c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [W22, g21_24]
  clear b21_90 w21_37c w21_378 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 g21_8 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_10 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0xEC
  obtain ⟨n23, c23, u23⟩ := s22.block svL2ec E22.self svL2ec_end
    ⟨trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0xEE (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svL2ec (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_8 : reg n23 (8 : Fin 32) = bl16 := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = cp := by
    rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = out := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = dg := by
    rw [rb23, runBlock_reg _ _ _ (20 : Fin 32) s22.zero (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = rootp := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = ll := by
    rw [rb23, runBlock_reg _ _ _ (22 : Fin 32) s22.zero (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = bp16 := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = lp := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_10 : reg n23 a0 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svL2ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_10, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m23]; exact w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := by rw [m23]; exact w22_84
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m23]; exact w22_88
  have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_8c
  have w23_27c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m23]; exact w22_27c
  have w23_378 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m23]; exact w22_378
  have w23_37c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m23]; exact w22_37c
  have b23_90 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m23]; exact b22_90
  clear w22_27c b22_90 w22_37c w22_378 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 rg22 W22 K22 fr22 s22 d22
  -- 0xEE: sw
  obtain ⟨n24, d24, s24, fr24, K24, W24, rg24⟩ := sv_sw F E23 s23 sv_at_ee (off' := 0xF2) (c := 0x280)
    (by decide) (by rw [g23_10]; sv_addr) (by decide) (by decide)
  have t24 : Steps n0 n24 := t23.trans d24
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.keep K24 (by decide)
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [rg24 sp, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg24 (3 : Fin 32), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg24 (4 : Fin 32), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = bl16 := by rw [rg24 (8 : Fin 32), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = cp := by rw [rg24 (9 : Fin 32), g23_9]
  have g24_10 : reg n24 a0 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by rw [rg24 a0, g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [rg24 (18 : Fin 32), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [rg24 (19 : Fin 32), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = dg := by rw [rg24 (20 : Fin 32), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = rootp := by rw [rg24 (21 : Fin 32), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = ll := by rw [rg24 (22 : Fin 32), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = bp16 := by rw [rg24 (23 : Fin 32), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg24 (24 : Fin 32), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg24 (25 : Fin 32), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = lp := by rw [rg24 (26 : Fin 32), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg24 (27 : Fin 32), g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4)] := keep_kk23.trans K24.toL
  clear keep_kk23
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K24.w32 (by decide) (by decide)).trans w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K24.w32 (by decide) (by decide)).trans w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := (K24.w32 (by decide) (by decide)).trans w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := (K24.w32 (by decide) (by decide)).trans w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K24.w32 (by decide) (by decide)).trans w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K24.w32 (by decide) (by decide)).trans w23_8c
  have w24_27c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K24.w32 (by decide) (by decide)).trans w23_27c
  have w24_378 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K24.w32 (by decide) (by decide)).trans w23_378
  have w24_37c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K24.w32 (by decide) (by decide)).trans w23_37c
  have b24_90 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K24.b8 (by decide) (by decide)).trans b23_90
  have w24_280 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [W24, g23_25]
  clear b23_90 w23_37c w23_378 w23_27c w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 g23_10 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0xF2: sw
  obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_f2 (off' := 0xF6) (c := 0x284)
    (by decide) (by rw [g24_10]; sv_addr) (by decide) (by decide)
  have t25 : Steps n0 n25 := t24.trans d25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = bl16 := by rw [rg25 (8 : Fin 32), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = cp := by rw [rg25 (9 : Fin 32), g24_9]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by rw [rg25 a0, g24_10]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = dg := by rw [rg25 (20 : Fin 32), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = rootp := by rw [rg25 (21 : Fin 32), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = ll := by rw [rg25 (22 : Fin 32), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = bp16 := by rw [rg25 (23 : Fin 32), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg25 (24 : Fin 32), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg25 (25 : Fin 32), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = lp := by rw [rg25 (26 : Fin 32), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg25 (27 : Fin 32), g24_27]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4)] := keep_kk24.trans K25.toL
  clear keep_kk24
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K25.w32 (by decide) (by decide)).trans w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K25.w32 (by decide) (by decide)).trans w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := (K25.w32 (by decide) (by decide)).trans w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := (K25.w32 (by decide) (by decide)).trans w24_84
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K25.w32 (by decide) (by decide)).trans w24_88
  have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K25.w32 (by decide) (by decide)).trans w24_8c
  have w25_27c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K25.w32 (by decide) (by decide)).trans w24_27c
  have w25_280 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K25.w32 (by decide) (by decide)).trans w24_280
  have w25_378 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K25.w32 (by decide) (by decide)).trans w24_378
  have w25_37c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K25.w32 (by decide) (by decide)).trans w24_37c
  have b25_90 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K25.b8 (by decide) (by decide)).trans b24_90
  have w25_284 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (cp) + BitVec.ofNat 32 tl1.header := by rw [W25, g24_24]
  clear w24_280 b24_90 w24_37c w24_378 w24_27c w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 rg24 W24 K24 fr24 s24 d24
  -- 0xF6: sw
  obtain ⟨n26, d26, s26, fr26, K26, W26, rg26⟩ := sv_sw F E25 s25 sv_at_f6 (off' := 0xFA) (c := 0x288)
    (by decide) (by rw [g25_10]; sv_addr) (by decide) (by decide)
  have t26 : Steps n0 n26 := t25.trans d26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [rg26 sp, g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg26 (3 : Fin 32), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg26 (4 : Fin 32), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = bl16 := by rw [rg26 (8 : Fin 32), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = cp := by rw [rg26 (9 : Fin 32), g25_9]
  have g26_10 : reg n26 a0 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by rw [rg26 a0, g25_10]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [rg26 (18 : Fin 32), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [rg26 (19 : Fin 32), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = dg := by rw [rg26 (20 : Fin 32), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = rootp := by rw [rg26 (21 : Fin 32), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = ll := by rw [rg26 (22 : Fin 32), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = bp16 := by rw [rg26 (23 : Fin 32), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg26 (24 : Fin 32), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg26 (25 : Fin 32), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = lp := by rw [rg26 (26 : Fin 32), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg26 (27 : Fin 32), g25_27]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4)] := keep_kk25.trans K26.toL
  clear keep_kk25
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K26.w32 (by decide) (by decide)).trans w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K26.w32 (by decide) (by decide)).trans w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := (K26.w32 (by decide) (by decide)).trans w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := (K26.w32 (by decide) (by decide)).trans w25_84
  have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K26.w32 (by decide) (by decide)).trans w25_88
  have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K26.w32 (by decide) (by decide)).trans w25_8c
  have w26_27c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K26.w32 (by decide) (by decide)).trans w25_27c
  have w26_280 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K26.w32 (by decide) (by decide)).trans w25_280
  have w26_284 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (cp) + BitVec.ofNat 32 tl1.header := (K26.w32 (by decide) (by decide)).trans w25_284
  have w26_378 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K26.w32 (by decide) (by decide)).trans w25_378
  have w26_37c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K26.w32 (by decide) (by decide)).trans w25_37c
  have b26_90 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K26.b8 (by decide) (by decide)).trans b25_90
  have w26_288 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = BitVec.ofNat 32 tl1.len := by rw [W26, g25_25]
  clear w25_284 b25_90 w25_37c w25_378 w25_280 w25_27c w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
  -- 0xFA
  obtain ⟨n27, c27, u27⟩ := s26.block svL2fa E26.self svL2fa_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem SV n27 0x102 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock svL2fa (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans c27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by
    rw [rb27, runBlock_reg _ _ _ sp s26.zero (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (3 : Fin 32) s26.zero (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (4 : Fin 32) s26.zero (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = bl16 := by
    rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = cp := by
    rw [rb27, runBlock_reg _ _ _ (9 : Fin 32) s26.zero (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by
    rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = dg := by
    rw [rb27, runBlock_reg _ _ _ (20 : Fin 32) s26.zero (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = rootp := by
    rw [rb27, runBlock_reg _ _ _ (21 : Fin 32) s26.zero (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = ll := by
    rw [rb27, runBlock_reg _ _ _ (22 : Fin 32) s26.zero (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = bp16 := by
    rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb27, runBlock_reg _ _ _ (25 : Fin 32) s26.zero (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = lp := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
  have g27_10 : reg n27 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svL2fa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_10, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g27_11 : reg n27 a1 = B + 0x21A0 + BitVec.ofNat 32 0x27C := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svL2fa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_10, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g27_12 : reg n27 a2 = BitVec.ofNat 32 0xA0 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svL2fa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_10, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m27]; exact w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m27]; exact w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp16 := by rw [m27]; exact w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl16 := by rw [m27]; exact w26_84
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m27]; exact w26_88
  have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m27]; exact w26_8c
  have w27_27c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m27]; exact w26_27c
  have w27_280 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m27]; exact w26_280
  have w27_284 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m27]; exact w26_284
  have w27_288 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = BitVec.ofNat 32 tl1.len := by rw [m27]; exact w26_288
  have w27_378 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m27]; exact w26_378
  have w27_37c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m27]; exact w26_37c
  have b27_90 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m27]; exact b26_90
  clear w26_288 b26_90 w26_37c w26_378 w26_284 w26_280 w26_27c w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 rg26 W26 K26 fr26 s26 d26
  -- 0x102: sv_optF
  obtain ⟨n28, c28, s28, sp28, rk28, K28, R28, fr28⟩ := sv_optF (oc := 0x80) (dc := 0x27C) (tag := 0xA0)
    F E27 s27 sv_at_102 sv_at_106 (by decide) (by decide) g27_2 g27_10 g27_11 g27_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w27_284 w27_288 (cc_in.contentW hr1)
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keepL K28 (by decide)
  rw [sv_mb fR27 (cc_in.contentW hr1)] at R28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rk28 sp (by decide) (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk28 (3 : Fin 32) (by decide) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk28 (4 : Fin 32) (by decide) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = bl16 := by rw [rk28 (8 : Fin 32) (by decide) (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = cp := by rw [rk28 (9 : Fin 32) (by decide) (by decide), g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rk28 (18 : Fin 32) (by decide) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rk28 (19 : Fin 32) (by decide) (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = dg := by rw [rk28 (20 : Fin 32) (by decide) (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = rootp := by rw [rk28 (21 : Fin 32) (by decide) (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = ll := by rw [rk28 (22 : Fin 32) (by decide) (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = bp16 := by rw [rk28 (23 : Fin 32) (by decide) (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rk28 (24 : Fin 32) (by decide) (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rk28 (25 : Fin 32) (by decide) (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = lp := by rw [rk28 (26 : Fin 32) (by decide) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rk28 (27 : Fin 32) (by decide) (by decide), g27_27]
  obtain ⟨r28, hr28⟩ : ∃ r, derOptRes 0xA0 (memBytes M0 ((cp) + BitVec.ofNat 32 tl1.header) (BitVec.ofNat 32 tl1.len).toNat) = r := ⟨_, rfl⟩
  rcases r28 with _ | (er28 | tl28)
  · rw [hr28] at R28
    obtain ⟨y0_28, y4_28⟩ := R28
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := keep_kk27.trans K28
    clear keep_kk27
    have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K28.w32 (by decide) (by decide)).trans w27_78
    have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K28.w32 (by decide) (by decide)).trans w27_7c
    have w28_27c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K28.w32 (by decide) (by decide)).trans w27_27c
    have w28_280 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K28.w32 (by decide) (by decide)).trans w27_280
    have w28_378 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K28.w32 (by decide) (by decide)).trans w27_378
    have w28_37c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K28.w32 (by decide) (by decide)).trans w27_37c
    have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = 0 := y4_28
    have b28_80 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := y0_28
    clear b27_90 w27_37c w27_378 w27_288 w27_284 w27_280 w27_27c w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 g27_12 g27_11 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
    -- 0x10A: lbu
    obtain ⟨n29, d29, u29⟩ := s28.lbu E28.self sv_at_10a (off' := 0x10E) (by decide)
    have s29 : St n29.mem SV n29 0x10E (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = bl16 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = cp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = dg := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = rootp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = ll := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = bp16 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = lp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
    have g29_10 : reg n29 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
      rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g28_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, b28_80]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m29]; exact w28_78
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m29]; exact w28_7c
    have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = 0 := by rw [m29]; exact w28_84
    have w29_27c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m29]; exact w28_27c
    have w29_280 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m29]; exact w28_280
    have w29_378 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m29]; exact w28_378
    have w29_37c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m29]; exact w28_37c
    have b29_80 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m29]; exact b28_80
    clear b28_80 w28_84 w28_37c w28_378 w28_280 w28_27c w28_7c w28_78 y4_28 y0_28
    -- 0x10E: branch, taken
    obtain ⟨n30, d30, u30⟩ := s29.taken E29.self 0x116 sv_at_10e
      (by decide) (by rw [g29_10, s29.zero]; rfl)
    have s30 : St n30.mem SV n30 0x116 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = bl16 := by rw [u30.regs, g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = cp := by rw [u30.regs, g29_9]
    have g30_10 : reg n30 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u30.regs, g29_10]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = dg := by rw [u30.regs, g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = rootp := by rw [u30.regs, g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = ll := by rw [u30.regs, g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = bp16 := by rw [u30.regs, g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u30.regs, g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u30.regs, g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = lp := by rw [u30.regs, g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u30.regs, g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m30]; exact w29_78
    have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m30]; exact w29_7c
    have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = 0 := by rw [m30]; exact w29_84
    have w30_27c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m30]; exact w29_27c
    have w30_280 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m30]; exact w29_280
    have w30_378 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_378
    have w30_37c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_37c
    have b30_80 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m30]; exact b29_80
    clear b29_80 w29_37c w29_378 w29_280 w29_27c w29_84 w29_7c w29_78 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
    -- 0x116: lw
    obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_116 (off' := 0x118) (by decide)
      (by rw [g30_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s31 : St n31.mem SV n31 0x118 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
    have g31_8 : reg n31 (8 : Fin 32) = bl16 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
    have g31_9 : reg n31 (9 : Fin 32) = cp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
    have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = dg := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = rootp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = ll := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = bp16 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = lp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
    have g31_10 : reg n31 a0 = 0 := by
      rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g30_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, w30_84]
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m31]; exact w30_78
    have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m31]; exact w30_7c
    have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = 0 := by rw [m31]; exact w30_84
    have w31_27c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m31]; exact w30_27c
    have w31_280 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m31]; exact w30_280
    have w31_378 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_378
    have w31_37c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_37c
    have b31_80 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m31]; exact b30_80
    clear b30_80 w30_37c w30_378 w30_280 w30_27c w30_84 w30_7c w30_78 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
    -- 0x118: branch, taken
    obtain ⟨n32, d32, u32⟩ := s31.taken E31.self 0x150 sv_at_118
      (by decide) (by rw [g31_10, s31.zero]; rfl)
    have s32 : St n32.mem SV n32 0x150 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
    have g32_8 : reg n32 (8 : Fin 32) = bl16 := by rw [u32.regs, g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = cp := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = 0 := by rw [u32.regs, g31_10]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = bp16 := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = lp := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m32]; exact w31_78
    have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m32]; exact w31_7c
    have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = 0 := by rw [m32]; exact w31_84
    have w32_27c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m32]; exact w31_27c
    have w32_280 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m32]; exact w31_280
    have w32_378 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_378
    have w32_37c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_37c
    have b32_80 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m32]; exact b31_80
    clear b31_80 w31_37c w31_378 w31_280 w31_27c w31_84 w31_7c w31_78 g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    -- 0x150
    obtain ⟨n33, c33, u33⟩ := s32.block svL2150 E32.self svL2150_end
      ⟨trivial, trivial⟩
    have m33 : n33.mem = n32.mem := u33.mem
    have s33 : St n33.mem SV n33 0x152 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
    have rb33 : ∀ q, reg n33 q = (runBlock svL2150 (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
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
    have g33_9 : reg n33 (9 : Fin 32) = cp := by
      rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
    have g33_10 : reg n33 a0 = 0 := by
      rw [rb33, runBlock_reg _ _ _ a0 s32.zero (by decide), g32_10]
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
    have g33_23 : reg n33 (23 : Fin 32) = bp16 := by
      rw [rb33, runBlock_reg _ _ _ (23 : Fin 32) s32.zero (by decide), g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
      rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by
      rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = lp := by
      rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
    have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb33]; simp +decide only [runBlock, BInstr.run, svL2150, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_10, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m33]; exact keep_kk32
    clear keep_kk32
    have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m33]; exact w32_78
    have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m33]; exact w32_7c
    have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = 0 := by rw [m33]; exact w32_84
    have w33_27c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m33]; exact w32_27c
    have w33_280 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m33]; exact w32_280
    have w33_378 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m33]; exact w32_378
    have w33_37c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m33]; exact w32_37c
    have b33_80 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m33]; exact b32_80
    clear b32_80 w32_37c w32_378 w32_280 w32_27c w32_84 w32_7c w32_78 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
    -- 0x152: j
    obtain ⟨n34, d34, u34⟩ := s33.jump E33.self sv_at_152 (off' := 0x7A4) (by decide)
      (by rw [s33.pc]; decide)
    have s34 : St n34.mem SV n34 0x7A4 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
    have m34 : n34.mem = n33.mem := u34.mem
    have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
    have t34 : Steps n0 n34 := t33.trans (.single d34)
    have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.same m34
    have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, g33_4]
    have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u34.regs, g33_8]
    have g34_9 : reg n34 (9 : Fin 32) = cp := by rw [u34.regs, g33_9]
    have g34_10 : reg n34 a0 = 0 := by rw [u34.regs, g33_10]
    have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, g33_18]
    have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, g33_19]
    have g34_20 : reg n34 (20 : Fin 32) = dg := by rw [u34.regs, g33_20]
    have g34_21 : reg n34 (21 : Fin 32) = rootp := by rw [u34.regs, g33_21]
    have g34_22 : reg n34 (22 : Fin 32) = ll := by rw [u34.regs, g33_22]
    have g34_23 : reg n34 (23 : Fin 32) = bp16 := by rw [u34.regs, g33_23]
    have g34_24 : reg n34 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u34.regs, g33_24]
    have g34_25 : reg n34 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u34.regs, g33_25]
    have g34_26 : reg n34 (26 : Fin 32) = lp := by rw [u34.regs, g33_26]
    have g34_27 : reg n34 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u34.regs, g33_27]
    have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m34]; exact keep_kk33
    clear keep_kk33
    have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m34]; exact w33_78
    have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m34]; exact w33_7c
    have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = 0 := by rw [m34]; exact w33_84
    have w34_27c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m34]; exact w33_27c
    have w34_280 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m34]; exact w33_280
    have w34_378 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m34]; exact w33_378
    have w34_37c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m34]; exact w33_37c
    have b34_80 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m34]; exact b33_80
    clear b33_80 w33_37c w33_378 w33_280 w33_27c w33_84 w33_7c w33_78 g33_8 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_10 g33_9 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', tl28', h5', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; rw [hr28] at h5'; cases h5'), sv_fail F E34 s34 t34 (fun x hx => (fR34 x hx).trans (fM x hx).symm) V34 hret g34_2 g34_18 hO g34_3 g34_4⟩
  · rw [hr28] at R28
    obtain ⟨y0_28, -⟩ := R28
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := keep_kk27.trans K28
    clear keep_kk27
    have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K28.w32 (by decide) (by decide)).trans w27_78
    have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K28.w32 (by decide) (by decide)).trans w27_7c
    have w28_27c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K28.w32 (by decide) (by decide)).trans w27_27c
    have w28_280 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K28.w32 (by decide) (by decide)).trans w27_280
    have w28_378 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K28.w32 (by decide) (by decide)).trans w27_378
    have w28_37c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K28.w32 (by decide) (by decide)).trans w27_37c
    have b28_80 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := y0_28
    clear b27_90 w27_37c w27_378 w27_288 w27_284 w27_280 w27_27c w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 g27_12 g27_11 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
    -- 0x10A: lbu
    obtain ⟨n29, d29, u29⟩ := s28.lbu E28.self sv_at_10a (off' := 0x10E) (by decide)
    have s29 : St n29.mem SV n29 0x10E (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = bl16 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = cp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = dg := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = rootp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = ll := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = bp16 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = lp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
    have g29_10 : reg n29 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g28_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, b28_80]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m29]; exact w28_78
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m29]; exact w28_7c
    have w29_27c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m29]; exact w28_27c
    have w29_280 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m29]; exact w28_280
    have w29_378 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m29]; exact w28_378
    have w29_37c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m29]; exact w28_37c
    have b29_80 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m29]; exact b28_80
    clear b28_80 w28_37c w28_378 w28_280 w28_27c w28_7c w28_78 y0_28
    -- 0x10E: branch, not taken
    obtain ⟨n30, d30, u30⟩ := s29.notTaken E29.self 0x110 sv_at_10e
      (by decide) (by rw [g29_10, s29.zero]; decide)
    have s30 : St n30.mem SV n30 0x110 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = bl16 := by rw [u30.regs, g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = cp := by rw [u30.regs, g29_9]
    have g30_10 : reg n30 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u30.regs, g29_10]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = dg := by rw [u30.regs, g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = rootp := by rw [u30.regs, g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = ll := by rw [u30.regs, g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = bp16 := by rw [u30.regs, g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u30.regs, g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u30.regs, g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = lp := by rw [u30.regs, g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u30.regs, g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m30]; exact w29_78
    have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m30]; exact w29_7c
    have w30_27c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m30]; exact w29_27c
    have w30_280 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m30]; exact w29_280
    have w30_378 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_378
    have w30_37c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_37c
    have b30_80 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m30]; exact b29_80
    clear b29_80 w29_37c w29_378 w29_280 w29_27c w29_7c w29_78 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
    -- 0x110: lbu
    obtain ⟨n31, d31, u31⟩ := s30.lbu E30.self sv_at_110 (off' := 0x114) (by decide)
    have s31 : St n31.mem SV n31 0x114 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
    have g31_9 : reg n31 (9 : Fin 32) = cp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
    have g31_10 : reg n31 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_10]
    have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = dg := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = rootp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = ll := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = bp16 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = lp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m31]; exact w30_78
    have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m31]; exact w30_7c
    have w31_27c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m31]; exact w30_27c
    have w31_280 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m31]; exact w30_280
    have w31_378 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_378
    have w31_37c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_37c
    have b31_80 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m31]; exact b30_80
    clear b30_80 w30_37c w30_378 w30_280 w30_27c w30_7c w30_78 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
    -- 0x114: j
    obtain ⟨n32, d32, u32⟩ := s31.jump E31.self sv_at_114 (off' := 0x7A4) (by decide)
      (by rw [s31.pc]; decide)
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
    have g32_9 : reg n32 (9 : Fin 32) = cp := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u32.regs, g31_10]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = bp16 := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = lp := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m32]; exact w31_78
    have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m32]; exact w31_7c
    have w32_27c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m32]; exact w31_27c
    have w32_280 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m32]; exact w31_280
    have w32_378 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_378
    have w32_37c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_37c
    have b32_80 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m32]; exact b31_80
    clear b31_80 w31_37c w31_378 w31_280 w31_27c w31_7c w31_78 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', tl28', h5', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; rw [hr28] at h5'; cases h5'), sv_fail F E32 s32 t32 (fun x hx => (fR32 x hx).trans (fM x hx).symm) V32 hret g32_2 g32_18 hO g32_3 g32_4⟩
  rw [hr28] at R28
  obtain ⟨y0_28, y4_28, y8_28, y12_28, y16_28, y20_28, d8_28, d12_28⟩ := R28
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := keep_kk27.trans K28
  clear keep_kk27
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K28.w32 (by decide) (by decide)).trans w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K28.w32 (by decide) (by decide)).trans w27_7c
  have w28_27c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K28.w32 (by decide) (by decide)).trans w27_27c
  have w28_280 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K28.w32 (by decide) (by decide)).trans w27_280
  have w28_378 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K28.w32 (by decide) (by decide)).trans w27_378
  have w28_37c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K28.w32 (by decide) (by decide)).trans w27_37c
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := y4_28
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := y8_28
  have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := y12_28
  have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := y16_28
  have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := d8_28
  have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := d12_28
  have b28_80 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := y0_28
  have b28_94 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := y20_28
  clear b27_90 w27_37c w27_378 w27_288 w27_284 w27_280 w27_27c w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 g27_12 g27_11 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
  -- 0x10A: lbu
  obtain ⟨n29, d29, u29⟩ := s28.lbu E28.self sv_at_10a (off' := 0x10E) (by decide)
  have s29 : St n29.mem SV n29 0x10E (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = bl16 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = cp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = dg := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = rootp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = ll := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = bp16 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = lp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
  have g29_10 : reg n29 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g28_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, b28_80]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m29]; exact w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m29]; exact w28_7c
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m29]; exact w28_84
  have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m29]; exact w28_88
  have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m29]; exact w28_8c
  have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m29]; exact w28_90
  have w29_27c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m29]; exact w28_27c
  have w29_280 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m29]; exact w28_280
  have w29_284 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m29]; exact w28_284
  have w29_288 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m29]; exact w28_288
  have w29_378 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m29]; exact w28_378
  have w29_37c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m29]; exact w28_37c
  have b29_80 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m29]; exact b28_80
  have b29_94 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m29]; exact b28_94
  clear b28_94 b28_80 w28_288 w28_284 w28_90 w28_8c w28_88 w28_84 w28_37c w28_378 w28_280 w28_27c w28_7c w28_78 d12_28 d8_28 y20_28 y16_28 y12_28 y8_28 y4_28 y0_28 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 K28 rk28 sp28 s28 c28
  -- 0x10E: branch, taken
  obtain ⟨n30, d30, u30⟩ := s29.taken E29.self 0x116 sv_at_10e
    (by decide) (by rw [g29_10, s29.zero]; rfl)
  have s30 : St n30.mem SV n30 0x116 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = bl16 := by rw [u30.regs, g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = cp := by rw [u30.regs, g29_9]
  have g30_10 : reg n30 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u30.regs, g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = dg := by rw [u30.regs, g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = rootp := by rw [u30.regs, g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = ll := by rw [u30.regs, g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = bp16 := by rw [u30.regs, g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u30.regs, g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u30.regs, g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = lp := by rw [u30.regs, g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u30.regs, g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m30]; exact w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m30]; exact w29_7c
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m30]; exact w29_84
  have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m30]; exact w29_88
  have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m30]; exact w29_8c
  have w30_90 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m30]; exact w29_90
  have w30_27c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m30]; exact w29_27c
  have w30_280 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m30]; exact w29_280
  have w30_284 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m30]; exact w29_284
  have w30_288 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m30]; exact w29_288
  have w30_378 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_378
  have w30_37c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_37c
  have b30_80 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m30]; exact b29_80
  have b30_94 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m30]; exact b29_94
  clear b29_94 b29_80 w29_37c w29_378 w29_288 w29_284 w29_280 w29_27c w29_90 w29_8c w29_88 w29_84 w29_7c w29_78 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  -- 0x116: lw
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_116 (off' := 0x118) (by decide)
    (by rw [g30_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s31 : St n31.mem SV n31 0x118 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = bl16 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = cp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = dg := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = rootp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = ll := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = bp16 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = lp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
  have g31_10 : reg n31 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, w30_84]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m31]; exact w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m31]; exact w30_7c
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m31]; exact w30_84
  have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m31]; exact w30_88
  have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m31]; exact w30_8c
  have w31_90 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m31]; exact w30_90
  have w31_27c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m31]; exact w30_27c
  have w31_280 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m31]; exact w30_280
  have w31_284 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m31]; exact w30_284
  have w31_288 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m31]; exact w30_288
  have w31_378 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_378
  have w31_37c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_37c
  have b31_80 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m31]; exact b30_80
  have b31_94 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m31]; exact b30_94
  clear b30_94 b30_80 w30_37c w30_378 w30_288 w30_284 w30_280 w30_27c w30_90 w30_8c w30_88 w30_84 w30_7c w30_78 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
  -- 0x118: branch, not taken
  obtain ⟨n32, d32, u32⟩ := s31.notTaken E31.self 0x11A sv_at_118
    (by decide) (by rw [g31_10, s31.zero]; exact br_beq_f ((cc_in.contentW hr1).ok_ne (opt_ok_elem hr28)))
  have s32 : St n32.mem SV n32 0x11A (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = bl16 := by rw [u32.regs, g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = cp := by rw [u32.regs, g31_9]
  have g32_10 : reg n32 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [u32.regs, g31_10]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = bp16 := by rw [u32.regs, g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u32.regs, g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u32.regs, g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = lp := by rw [u32.regs, g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u32.regs, g31_27]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m32]; exact w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m32]; exact w31_7c
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m32]; exact w31_84
  have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m32]; exact w31_88
  have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m32]; exact w31_8c
  have w32_90 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m32]; exact w31_90
  have w32_27c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m32]; exact w31_27c
  have w32_280 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m32]; exact w31_280
  have w32_284 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m32]; exact w31_284
  have w32_288 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m32]; exact w31_288
  have w32_378 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_378
  have w32_37c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_37c
  have b32_80 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m32]; exact b31_80
  have b32_94 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m32]; exact b31_94
  clear b31_94 b31_80 w31_37c w31_378 w31_288 w31_284 w31_280 w31_27c w31_90 w31_8c w31_88 w31_84 w31_7c w31_78 g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0x11A
  obtain ⟨n33, c33, u33⟩ := s32.block svL211a E32.self svL211a_end
    ⟨trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem SV n33 0x11C (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock svL211a (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
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
  have g33_8 : reg n33 (8 : Fin 32) = bl16 := by
    rw [rb33, runBlock_reg _ _ _ (8 : Fin 32) s32.zero (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = cp := by
    rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
  have g33_10 : reg n33 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by
    rw [rb33, runBlock_reg _ _ _ a0 s32.zero (by decide), g32_10]
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
  have g33_23 : reg n33 (23 : Fin 32) = bp16 := by
    rw [rb33, runBlock_reg _ _ _ (23 : Fin 32) s32.zero (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
  have g33_26 : reg n33 (26 : Fin 32) = lp := by
    rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
  have g33_25 : reg n33 (25 : Fin 32) = bl16 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svL211a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_10, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m33]; exact w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m33]; exact w32_7c
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m33]; exact w32_84
  have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m33]; exact w32_88
  have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m33]; exact w32_8c
  have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m33]; exact w32_90
  have w33_27c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m33]; exact w32_27c
  have w33_280 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m33]; exact w32_280
  have w33_284 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m33]; exact w32_284
  have w33_288 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m33]; exact w32_288
  have w33_378 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m33]; exact w32_378
  have w33_37c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m33]; exact w32_37c
  have b33_80 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m33]; exact b32_80
  have b33_94 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m33]; exact b32_94
  clear b32_94 b32_80 w32_37c w32_378 w32_288 w32_284 w32_280 w32_27c w32_90 w32_8c w32_88 w32_84 w32_7c w32_78 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0x11C: lw
  obtain ⟨n34, d34, u34⟩ := s33.lw E33.self sv_at_11c (off' := 0x11E) (by decide)
    (by rw [g33_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s34 : St n34.mem SV n34 0x11E (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans (.single d34)
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = bl16 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = cp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_9]
  have g34_10 : reg n34 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [u34.regs, upd_ne (by decide) (by decide), g33_10]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, upd_ne (by decide) (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = dg := by rw [u34.regs, upd_ne (by decide) (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = rootp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = ll := by rw [u34.regs, upd_ne (by decide) (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = bp16 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u34.regs, upd_ne (by decide) (by decide), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = bl16 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = lp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_27]
  have g34_11 : reg n34 a1 = BitVec.ofNat 32 tl28.len := by
    rw [u34.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g33_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr, w33_88]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m34]; exact w33_78
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m34]; exact w33_7c
  have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m34]; exact w33_84
  have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m34]; exact w33_88
  have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m34]; exact w33_8c
  have w34_90 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m34]; exact w33_90
  have w34_27c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m34]; exact w33_27c
  have w34_280 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m34]; exact w33_280
  have w34_284 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m34]; exact w33_284
  have w34_288 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m34]; exact w33_288
  have w34_378 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m34]; exact w33_378
  have w34_37c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m34]; exact w33_37c
  have b34_80 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m34]; exact b33_80
  have b34_94 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m34]; exact b33_94
  clear b33_94 b33_80 w33_37c w33_378 w33_288 w33_284 w33_280 w33_27c w33_90 w33_8c w33_88 w33_84 w33_7c w33_78 g33_25 g33_27 g33_26 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_10 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
  -- 0x11E
  obtain ⟨n35, c35, u35⟩ := s34.block svL211e E34.self svL211e_end
    ⟨trivial, trivial⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have s35 : St n35.mem SV n35 0x120 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have rb35 : ∀ q, reg n35 q = (runBlock svL211e (n34.mem, reg n34)).2 q := fun q => by rw [u35.regs]
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans c35
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by
    rw [rb35, runBlock_reg _ _ _ sp s34.zero (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (3 : Fin 32) s34.zero (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (4 : Fin 32) s34.zero (by decide), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = bl16 := by
    rw [rb35, runBlock_reg _ _ _ (8 : Fin 32) s34.zero (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = cp := by
    rw [rb35, runBlock_reg _ _ _ (9 : Fin 32) s34.zero (by decide), g34_9]
  have g35_10 : reg n35 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by
    rw [rb35, runBlock_reg _ _ _ a0 s34.zero (by decide), g34_10]
  have g35_11 : reg n35 a1 = BitVec.ofNat 32 tl28.len := by
    rw [rb35, runBlock_reg _ _ _ a1 s34.zero (by decide), g34_11]
  have g35_18 : reg n35 (18 : Fin 32) = out := by
    rw [rb35, runBlock_reg _ _ _ (18 : Fin 32) s34.zero (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by
    rw [rb35, runBlock_reg _ _ _ (19 : Fin 32) s34.zero (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = dg := by
    rw [rb35, runBlock_reg _ _ _ (20 : Fin 32) s34.zero (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = rootp := by
    rw [rb35, runBlock_reg _ _ _ (21 : Fin 32) s34.zero (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = ll := by
    rw [rb35, runBlock_reg _ _ _ (22 : Fin 32) s34.zero (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = bp16 := by
    rw [rb35, runBlock_reg _ _ _ (23 : Fin 32) s34.zero (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb35, runBlock_reg _ _ _ (24 : Fin 32) s34.zero (by decide), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = bl16 := by
    rw [rb35, runBlock_reg _ _ _ (25 : Fin 32) s34.zero (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = lp := by
    rw [rb35, runBlock_reg _ _ _ (26 : Fin 32) s34.zero (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb35, runBlock_reg _ _ _ (27 : Fin 32) s34.zero (by decide), g34_27]
  have g35_12 : reg n35 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, svL211e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_10, g34_11, g34_18, g34_19, g34_20, g34_21, g34_22, g34_23, g34_24, g34_25, g34_26, g34_27, s34.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m35]; exact w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m35]; exact w34_7c
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m35]; exact w34_84
  have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m35]; exact w34_88
  have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m35]; exact w34_8c
  have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m35]; exact w34_90
  have w35_27c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m35]; exact w34_27c
  have w35_280 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m35]; exact w34_280
  have w35_284 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m35]; exact w34_284
  have w35_288 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m35]; exact w34_288
  have w35_378 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m35]; exact w34_378
  have w35_37c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m35]; exact w34_37c
  have b35_80 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m35]; exact b34_80
  have b35_94 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m35]; exact b34_94
  clear b34_94 b34_80 w34_37c w34_378 w34_288 w34_284 w34_280 w34_27c w34_90 w34_8c w34_88 w34_84 w34_7c w34_78 g34_11 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_10 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
  -- 0x120: sw
  obtain ⟨n36, d36, s36, fr36, K36, W36, rg36⟩ := sv_sw F E35 s35 sv_at_120 (off' := 0x122) (c := 0x25C)
    (by decide) (by rw [g35_12]; sv_addr) (by decide) (by decide)
  have t36 : Steps n0 n36 := t35.trans d36
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.keep K36 (by decide)
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [rg36 sp, g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg36 (3 : Fin 32), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg36 (4 : Fin 32), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = bl16 := by rw [rg36 (8 : Fin 32), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = cp := by rw [rg36 (9 : Fin 32), g35_9]
  have g36_10 : reg n36 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [rg36 a0, g35_10]
  have g36_11 : reg n36 a1 = BitVec.ofNat 32 tl28.len := by rw [rg36 a1, g35_11]
  have g36_12 : reg n36 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg36 a2, g35_12]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [rg36 (18 : Fin 32), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [rg36 (19 : Fin 32), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = dg := by rw [rg36 (20 : Fin 32), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = rootp := by rw [rg36 (21 : Fin 32), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = ll := by rw [rg36 (22 : Fin 32), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = bp16 := by rw [rg36 (23 : Fin 32), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg36 (24 : Fin 32), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = bl16 := by rw [rg36 (25 : Fin 32), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = lp := by rw [rg36 (26 : Fin 32), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg36 (27 : Fin 32), g35_27]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4)] := keep_kk35.trans K36.toL
  clear keep_kk35
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K36.w32 (by decide) (by decide)).trans w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K36.w32 (by decide) (by decide)).trans w35_7c
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K36.w32 (by decide) (by decide)).trans w35_84
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := (K36.w32 (by decide) (by decide)).trans w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := (K36.w32 (by decide) (by decide)).trans w35_8c
  have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := (K36.w32 (by decide) (by decide)).trans w35_90
  have w36_27c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K36.w32 (by decide) (by decide)).trans w35_27c
  have w36_280 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K36.w32 (by decide) (by decide)).trans w35_280
  have w36_284 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := (K36.w32 (by decide) (by decide)).trans w35_284
  have w36_288 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := (K36.w32 (by decide) (by decide)).trans w35_288
  have w36_378 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K36.w32 (by decide) (by decide)).trans w35_378
  have w36_37c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K36.w32 (by decide) (by decide)).trans w35_37c
  have b36_80 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := (K36.b8 (by decide) (by decide)).trans b35_80
  have b36_94 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := (K36.b8 (by decide) (by decide)).trans b35_94
  have w36_25c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [W36, g35_10]
  clear b35_94 b35_80 w35_37c w35_378 w35_288 w35_284 w35_280 w35_27c w35_90 w35_8c w35_88 w35_84 w35_7c w35_78 g35_12 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_11 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 rb35 s35 m35 u35 c35
  -- 0x122: sw
  obtain ⟨n37, d37, s37, fr37, K37, W37, rg37⟩ := sv_sw F E36 s36 sv_at_122 (off' := 0x124) (c := 0x260)
    (by decide) (by rw [g36_12]; sv_addr) (by decide) (by decide)
  have t37 : Steps n0 n37 := t36.trans d37
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.keep K37 (by decide)
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [rg37 sp, g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg37 (3 : Fin 32), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg37 (4 : Fin 32), g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = bl16 := by rw [rg37 (8 : Fin 32), g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = cp := by rw [rg37 (9 : Fin 32), g36_9]
  have g37_10 : reg n37 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [rg37 a0, g36_10]
  have g37_11 : reg n37 a1 = BitVec.ofNat 32 tl28.len := by rw [rg37 a1, g36_11]
  have g37_12 : reg n37 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg37 a2, g36_12]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [rg37 (18 : Fin 32), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [rg37 (19 : Fin 32), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = dg := by rw [rg37 (20 : Fin 32), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = rootp := by rw [rg37 (21 : Fin 32), g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = ll := by rw [rg37 (22 : Fin 32), g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = bp16 := by rw [rg37 (23 : Fin 32), g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg37 (24 : Fin 32), g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = bl16 := by rw [rg37 (25 : Fin 32), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = lp := by rw [rg37 (26 : Fin 32), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg37 (27 : Fin 32), g36_27]
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4)] := keep_kk36.trans K37.toL
  clear keep_kk36
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K37.w32 (by decide) (by decide)).trans w36_78
  have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K37.w32 (by decide) (by decide)).trans w36_7c
  have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K37.w32 (by decide) (by decide)).trans w36_84
  have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := (K37.w32 (by decide) (by decide)).trans w36_88
  have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := (K37.w32 (by decide) (by decide)).trans w36_8c
  have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := (K37.w32 (by decide) (by decide)).trans w36_90
  have w37_25c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K37.w32 (by decide) (by decide)).trans w36_25c
  have w37_27c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K37.w32 (by decide) (by decide)).trans w36_27c
  have w37_280 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K37.w32 (by decide) (by decide)).trans w36_280
  have w37_284 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := (K37.w32 (by decide) (by decide)).trans w36_284
  have w37_288 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := (K37.w32 (by decide) (by decide)).trans w36_288
  have w37_378 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K37.w32 (by decide) (by decide)).trans w36_378
  have w37_37c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K37.w32 (by decide) (by decide)).trans w36_37c
  have b37_80 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := (K37.b8 (by decide) (by decide)).trans b36_80
  have b37_94 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := (K37.b8 (by decide) (by decide)).trans b36_94
  have w37_260 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [W37, g36_11]
  clear w36_25c b36_94 b36_80 w36_37c w36_378 w36_288 w36_284 w36_280 w36_27c w36_90 w36_8c w36_88 w36_84 w36_7c w36_78 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_12 g36_11 g36_10 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 rg36 W36 K36 fr36 s36 d36
  -- 0x124: sw
  obtain ⟨n38, d38, s38, fr38, K38, W38, rg38⟩ := sv_sw F E37 s37 sv_at_124 (off' := 0x126) (c := 0x264)
    (by decide) (by rw [g37_12]; sv_addr) (by decide) (by decide)
  have t38 : Steps n0 n38 := t37.trans d38
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.keep K38 (by decide)
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [rg38 sp, g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg38 (3 : Fin 32), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg38 (4 : Fin 32), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = bl16 := by rw [rg38 (8 : Fin 32), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = cp := by rw [rg38 (9 : Fin 32), g37_9]
  have g38_10 : reg n38 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [rg38 a0, g37_10]
  have g38_11 : reg n38 a1 = BitVec.ofNat 32 tl28.len := by rw [rg38 a1, g37_11]
  have g38_12 : reg n38 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg38 a2, g37_12]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [rg38 (18 : Fin 32), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [rg38 (19 : Fin 32), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = dg := by rw [rg38 (20 : Fin 32), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = rootp := by rw [rg38 (21 : Fin 32), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = ll := by rw [rg38 (22 : Fin 32), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = bp16 := by rw [rg38 (23 : Fin 32), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg38 (24 : Fin 32), g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = bl16 := by rw [rg38 (25 : Fin 32), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = lp := by rw [rg38 (26 : Fin 32), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg38 (27 : Fin 32), g37_27]
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4)] := keep_kk37.trans K38.toL
  clear keep_kk37
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K38.w32 (by decide) (by decide)).trans w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K38.w32 (by decide) (by decide)).trans w37_7c
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K38.w32 (by decide) (by decide)).trans w37_84
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := (K38.w32 (by decide) (by decide)).trans w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := (K38.w32 (by decide) (by decide)).trans w37_8c
  have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := (K38.w32 (by decide) (by decide)).trans w37_90
  have w38_25c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K38.w32 (by decide) (by decide)).trans w37_25c
  have w38_260 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := (K38.w32 (by decide) (by decide)).trans w37_260
  have w38_27c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K38.w32 (by decide) (by decide)).trans w37_27c
  have w38_280 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K38.w32 (by decide) (by decide)).trans w37_280
  have w38_284 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := (K38.w32 (by decide) (by decide)).trans w37_284
  have w38_288 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := (K38.w32 (by decide) (by decide)).trans w37_288
  have w38_378 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K38.w32 (by decide) (by decide)).trans w37_378
  have w38_37c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K38.w32 (by decide) (by decide)).trans w37_37c
  have b38_80 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := (K38.b8 (by decide) (by decide)).trans b37_80
  have b38_94 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := (K38.b8 (by decide) (by decide)).trans b37_94
  have w38_264 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [W38, g37_10]
  clear w37_260 b37_94 b37_80 w37_37c w37_378 w37_288 w37_284 w37_280 w37_27c w37_25c w37_90 w37_8c w37_88 w37_84 w37_7c w37_78 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_12 g37_11 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 rg37 W37 K37 fr37 s37 d37
  -- 0x126: sw
  obtain ⟨n39, d39, s39, fr39, K39, W39, rg39⟩ := sv_sw F E38 s38 sv_at_126 (off' := 0x128) (c := 0x268)
    (by decide) (by rw [g38_12]; sv_addr) (by decide) (by decide)
  have t39 : Steps n0 n39 := t38.trans d39
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.keep K39 (by decide)
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [rg39 sp, g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg39 (3 : Fin 32), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg39 (4 : Fin 32), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = bl16 := by rw [rg39 (8 : Fin 32), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = cp := by rw [rg39 (9 : Fin 32), g38_9]
  have g39_10 : reg n39 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [rg39 a0, g38_10]
  have g39_11 : reg n39 a1 = BitVec.ofNat 32 tl28.len := by rw [rg39 a1, g38_11]
  have g39_12 : reg n39 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg39 a2, g38_12]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [rg39 (18 : Fin 32), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [rg39 (19 : Fin 32), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = dg := by rw [rg39 (20 : Fin 32), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = rootp := by rw [rg39 (21 : Fin 32), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = ll := by rw [rg39 (22 : Fin 32), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = bp16 := by rw [rg39 (23 : Fin 32), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg39 (24 : Fin 32), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = bl16 := by rw [rg39 (25 : Fin 32), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = lp := by rw [rg39 (26 : Fin 32), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg39 (27 : Fin 32), g38_27]
  have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := keep_kk38.trans K39.toL
  clear keep_kk38
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K39.w32 (by decide) (by decide)).trans w38_78
  have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K39.w32 (by decide) (by decide)).trans w38_7c
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K39.w32 (by decide) (by decide)).trans w38_84
  have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := (K39.w32 (by decide) (by decide)).trans w38_88
  have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := (K39.w32 (by decide) (by decide)).trans w38_8c
  have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := (K39.w32 (by decide) (by decide)).trans w38_90
  have w39_25c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K39.w32 (by decide) (by decide)).trans w38_25c
  have w39_260 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := (K39.w32 (by decide) (by decide)).trans w38_260
  have w39_264 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K39.w32 (by decide) (by decide)).trans w38_264
  have w39_27c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K39.w32 (by decide) (by decide)).trans w38_27c
  have w39_280 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K39.w32 (by decide) (by decide)).trans w38_280
  have w39_284 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := (K39.w32 (by decide) (by decide)).trans w38_284
  have w39_288 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := (K39.w32 (by decide) (by decide)).trans w38_288
  have w39_378 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K39.w32 (by decide) (by decide)).trans w38_378
  have w39_37c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K39.w32 (by decide) (by decide)).trans w38_37c
  have b39_80 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := (K39.b8 (by decide) (by decide)).trans b38_80
  have b39_94 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := (K39.b8 (by decide) (by decide)).trans b38_94
  have w39_268 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl28.len := by rw [W39, g38_11]
  clear w38_264 b38_94 b38_80 w38_37c w38_378 w38_288 w38_284 w38_280 w38_27c w38_260 w38_25c w38_90 w38_8c w38_88 w38_84 w38_7c w38_78 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_12 g38_11 g38_10 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 rg38 W38 K38 fr38 s38 d38
  -- 0x128
  obtain ⟨n40, c40, u40⟩ := s39.block svL2128 E39.self svL2128_end
    ⟨trivial, trivial, trivial⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have s40 : St n40.mem SV n40 0x12C (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have rb40 : ∀ q, reg n40 q = (runBlock svL2128 (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
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
  have g40_8 : reg n40 (8 : Fin 32) = bl16 := by
    rw [rb40, runBlock_reg _ _ _ (8 : Fin 32) s39.zero (by decide), g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = cp := by
    rw [rb40, runBlock_reg _ _ _ (9 : Fin 32) s39.zero (by decide), g39_9]
  have g40_12 : reg n40 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb40, runBlock_reg _ _ _ a2 s39.zero (by decide), g39_12]
  have g40_18 : reg n40 (18 : Fin 32) = out := by
    rw [rb40, runBlock_reg _ _ _ (18 : Fin 32) s39.zero (by decide), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by
    rw [rb40, runBlock_reg _ _ _ (19 : Fin 32) s39.zero (by decide), g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = dg := by
    rw [rb40, runBlock_reg _ _ _ (20 : Fin 32) s39.zero (by decide), g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = rootp := by
    rw [rb40, runBlock_reg _ _ _ (21 : Fin 32) s39.zero (by decide), g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = ll := by
    rw [rb40, runBlock_reg _ _ _ (22 : Fin 32) s39.zero (by decide), g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = bp16 := by
    rw [rb40, runBlock_reg _ _ _ (23 : Fin 32) s39.zero (by decide), g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb40, runBlock_reg _ _ _ (24 : Fin 32) s39.zero (by decide), g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = bl16 := by
    rw [rb40, runBlock_reg _ _ _ (25 : Fin 32) s39.zero (by decide), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = lp := by
    rw [rb40, runBlock_reg _ _ _ (26 : Fin 32) s39.zero (by decide), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb40, runBlock_reg _ _ _ (27 : Fin 32) s39.zero (by decide), g39_27]
  have g40_10 : reg n40 a0 = B + 0x21A0 + BitVec.ofNat 32 0x25C := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svL2128, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_11, g39_12, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g40_11 : reg n40 a1 = BitVec.ofNat 32 0x2 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svL2128, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_11, g39_12, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := by rw [m40]; exact keep_kk39
  clear keep_kk39
  have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m40]; exact w39_78
  have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m40]; exact w39_7c
  have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m40]; exact w39_84
  have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m40]; exact w39_88
  have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m40]; exact w39_8c
  have w40_90 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m40]; exact w39_90
  have w40_25c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m40]; exact w39_25c
  have w40_260 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m40]; exact w39_260
  have w40_264 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m40]; exact w39_264
  have w40_268 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl28.len := by rw [m40]; exact w39_268
  have w40_27c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m40]; exact w39_27c
  have w40_280 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m40]; exact w39_280
  have w40_284 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m40]; exact w39_284
  have w40_288 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m40]; exact w39_288
  have w40_378 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m40]; exact w39_378
  have w40_37c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m40]; exact w39_37c
  have b40_80 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m40]; exact b39_80
  have b40_94 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m40]; exact b39_94
  clear w39_268 b39_94 b39_80 w39_37c w39_378 w39_288 w39_284 w39_280 w39_27c w39_264 w39_260 w39_25c w39_90 w39_8c w39_88 w39_84 w39_7c w39_78 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_12 g39_11 g39_10 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 rg39 W39 K39 fr39 s39 d39
  -- 0x12C: sv_iiF
  obtain ⟨n41, c41, s41, sp41, rk41, K41, A41, R41, fr41⟩ := sv_iiF (dc := 0x25C)
    F E40 s40 sv_at_12c sv_at_130 (by decide) (by decide) g40_2 g40_10
    (by decide) (by decide) w40_264 w40_268 ((cc_in.contentW hr1).contentW (opt_ok_elem hr28))
  have t41 : Steps n0 n41 := t40.trans c41
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.keepL K41 (by decide)
  rw [sv_mb fR40 ((cc_in.contentW hr1).contentW (opt_ok_elem hr28)), derIntIsOf_congr fR40 ((cc_in.contentW hr1).contentW (opt_ok_elem hr28)), g40_11] at R41
  rw [sv_mb fR40 ((cc_in.contentW hr1).contentW (opt_ok_elem hr28))] at A41
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk41 (3 : Fin 32) (by decide), g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk41 (4 : Fin 32) (by decide), g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = bl16 := by rw [rk41 (8 : Fin 32) (by decide), g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = cp := by rw [rk41 (9 : Fin 32) (by decide), g40_9]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [rk41 (18 : Fin 32) (by decide), g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [rk41 (19 : Fin 32) (by decide), g40_19]
  have g41_20 : reg n41 (20 : Fin 32) = dg := by rw [rk41 (20 : Fin 32) (by decide), g40_20]
  have g41_21 : reg n41 (21 : Fin 32) = rootp := by rw [rk41 (21 : Fin 32) (by decide), g40_21]
  have g41_22 : reg n41 (22 : Fin 32) = ll := by rw [rk41 (22 : Fin 32) (by decide), g40_22]
  have g41_23 : reg n41 (23 : Fin 32) = bp16 := by rw [rk41 (23 : Fin 32) (by decide), g40_23]
  have g41_24 : reg n41 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rk41 (24 : Fin 32) (by decide), g40_24]
  have g41_25 : reg n41 (25 : Fin 32) = bl16 := by rw [rk41 (25 : Fin 32) (by decide), g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = lp := by rw [rk41 (26 : Fin 32) (by decide), g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rk41 (27 : Fin 32) (by decide), g40_27]
  have g41_2 : reg n41 sp = B + 0x21A0 := sp41
  obtain ⟨r41, hr41⟩ : ∃ r, derIntIsOf M0 (memBytes M0 (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) (BitVec.ofNat 32 tl28.len).toNat) (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) (derElement 2 (memBytes M0 (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) (BitVec.ofNat 32 tl28.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = r := ⟨_, rfl⟩
  rcases r41 with b41 | (_ | _)
  · rw [hr41] at R41
    obtain ⟨a0_41, a1_41⟩ := R41
    have g41_10 : reg n41 a0 = BitVec.ofNat 32 0x1 := a0_41
    have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := keep_kk40.trans K41
    clear keep_kk40
    have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K41.w32 (by decide) (by decide)).trans w40_78
    have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K41.w32 (by decide) (by decide)).trans w40_7c
    have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K41.w32 (by decide) (by decide)).trans w40_84
    have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := (K41.w32 (by decide) (by decide)).trans w40_88
    have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := (K41.w32 (by decide) (by decide)).trans w40_8c
    have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := (K41.w32 (by decide) (by decide)).trans w40_90
    have w41_25c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K41.w32 (by decide) (by decide)).trans w40_25c
    have w41_260 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := (K41.w32 (by decide) (by decide)).trans w40_260
    have w41_27c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K41.w32 (by decide) (by decide)).trans w40_27c
    have w41_280 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K41.w32 (by decide) (by decide)).trans w40_280
    have w41_284 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := (K41.w32 (by decide) (by decide)).trans w40_284
    have w41_288 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := (K41.w32 (by decide) (by decide)).trans w40_288
    have w41_378 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K41.w32 (by decide) (by decide)).trans w40_378
    have w41_37c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K41.w32 (by decide) (by decide)).trans w40_37c
    have b41_80 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := (K41.b8 (by decide) (by decide)).trans b40_80
    have b41_94 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := (K41.b8 (by decide) (by decide)).trans b40_94
    clear b40_94 b40_80 w40_37c w40_378 w40_288 w40_284 w40_280 w40_27c w40_268 w40_264 w40_260 w40_25c w40_90 w40_8c w40_88 w40_84 w40_7c w40_78 g40_11 g40_10 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_12 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
    -- 0x134
    obtain ⟨n42, c42, u42⟩ := s41.block svL2134 E41.self svL2134_end
      ⟨trivial, trivial, trivial⟩
    have m42 : n42.mem = n41.mem := u42.mem
    have s42 : St n42.mem SV n42 0x138 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
    have rb42 : ∀ q, reg n42 q = (runBlock svL2134 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
    have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
    have t42 : Steps n0 n42 := t41.trans c42
    have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
    have E42 : SvCode n42.mem := E41.fr F fr42
    have V42 : SvSaves B n42.mem v := V41.same m42
    have g42_2 : reg n42 sp = B + 0x21A0 := by
      rw [rb42, runBlock_reg _ _ _ sp s41.zero (by decide), g41_2]
    have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb42, runBlock_reg _ _ _ (3 : Fin 32) s41.zero (by decide), g41_3]
    have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb42, runBlock_reg _ _ _ (4 : Fin 32) s41.zero (by decide), g41_4]
    have g42_9 : reg n42 (9 : Fin 32) = cp := by
      rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
    have g42_18 : reg n42 (18 : Fin 32) = out := by
      rw [rb42, runBlock_reg _ _ _ (18 : Fin 32) s41.zero (by decide), g41_18]
    have g42_19 : reg n42 (19 : Fin 32) = bp := by
      rw [rb42, runBlock_reg _ _ _ (19 : Fin 32) s41.zero (by decide), g41_19]
    have g42_20 : reg n42 (20 : Fin 32) = dg := by
      rw [rb42, runBlock_reg _ _ _ (20 : Fin 32) s41.zero (by decide), g41_20]
    have g42_21 : reg n42 (21 : Fin 32) = rootp := by
      rw [rb42, runBlock_reg _ _ _ (21 : Fin 32) s41.zero (by decide), g41_21]
    have g42_22 : reg n42 (22 : Fin 32) = ll := by
      rw [rb42, runBlock_reg _ _ _ (22 : Fin 32) s41.zero (by decide), g41_22]
    have g42_23 : reg n42 (23 : Fin 32) = bp16 := by
      rw [rb42, runBlock_reg _ _ _ (23 : Fin 32) s41.zero (by decide), g41_23]
    have g42_24 : reg n42 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
      rw [rb42, runBlock_reg _ _ _ (24 : Fin 32) s41.zero (by decide), g41_24]
    have g42_25 : reg n42 (25 : Fin 32) = bl16 := by
      rw [rb42, runBlock_reg _ _ _ (25 : Fin 32) s41.zero (by decide), g41_25]
    have g42_26 : reg n42 (26 : Fin 32) = lp := by
      rw [rb42, runBlock_reg _ _ _ (26 : Fin 32) s41.zero (by decide), g41_26]
    have g42_27 : reg n42 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb42, runBlock_reg _ _ _ (27 : Fin 32) s41.zero (by decide), g41_27]
    have g42_10 : reg n42 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb42]; simp +decide only [runBlock, BInstr.run, svL2134, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m42]; exact keep_kk41
    clear keep_kk41
    have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m42]; exact w41_78
    have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m42]; exact w41_7c
    have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m42]; exact w41_84
    have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m42]; exact w41_88
    have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m42]; exact w41_8c
    have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m42]; exact w41_90
    have w42_25c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m42]; exact w41_25c
    have w42_260 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m42]; exact w41_260
    have w42_27c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m42]; exact w41_27c
    have w42_280 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m42]; exact w41_280
    have w42_284 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m42]; exact w41_284
    have w42_288 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m42]; exact w41_288
    have w42_378 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m42]; exact w41_378
    have w42_37c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m42]; exact w41_37c
    have b42_80 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m42]; exact b41_80
    have b42_94 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m42]; exact b41_94
    clear b41_94 b41_80 w41_37c w41_378 w41_288 w41_284 w41_280 w41_27c w41_260 w41_25c w41_90 w41_8c w41_88 w41_84 w41_7c w41_78 g41_10 a1_41 a0_41
    -- 0x138: branch, taken
    obtain ⟨n43, d43, u43⟩ := s42.taken E42.self 0x7A4 sv_at_138
      (by decide) (by rw [g42_10, s42.zero]; decide)
    have s43 : St n43.mem SV n43 0x7A4 (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
    have m43 : n43.mem = n42.mem := u43.mem
    have fr43 : ∀ x, SvR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
    have t43 : Steps n0 n43 := t42.trans (.single d43)
    have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
    have E43 : SvCode n43.mem := E42.fr F fr43
    have V43 : SvSaves B n43.mem v := V42.same m43
    have g43_2 : reg n43 sp = B + 0x21A0 := by rw [u43.regs, g42_2]
    have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u43.regs, g42_3]
    have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u43.regs, g42_4]
    have g43_9 : reg n43 (9 : Fin 32) = cp := by rw [u43.regs, g42_9]
    have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x1 := by rw [u43.regs, g42_10]
    have g43_18 : reg n43 (18 : Fin 32) = out := by rw [u43.regs, g42_18]
    have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [u43.regs, g42_19]
    have g43_20 : reg n43 (20 : Fin 32) = dg := by rw [u43.regs, g42_20]
    have g43_21 : reg n43 (21 : Fin 32) = rootp := by rw [u43.regs, g42_21]
    have g43_22 : reg n43 (22 : Fin 32) = ll := by rw [u43.regs, g42_22]
    have g43_23 : reg n43 (23 : Fin 32) = bp16 := by rw [u43.regs, g42_23]
    have g43_24 : reg n43 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u43.regs, g42_24]
    have g43_25 : reg n43 (25 : Fin 32) = bl16 := by rw [u43.regs, g42_25]
    have g43_26 : reg n43 (26 : Fin 32) = lp := by rw [u43.regs, g42_26]
    have g43_27 : reg n43 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u43.regs, g42_27]
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m43]; exact keep_kk42
    clear keep_kk42
    have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m43]; exact w42_78
    have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m43]; exact w42_7c
    have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m43]; exact w42_84
    have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m43]; exact w42_88
    have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m43]; exact w42_8c
    have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m43]; exact w42_90
    have w43_25c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m43]; exact w42_25c
    have w43_260 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m43]; exact w42_260
    have w43_27c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m43]; exact w42_27c
    have w43_280 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m43]; exact w42_280
    have w43_284 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m43]; exact w42_284
    have w43_288 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m43]; exact w42_288
    have w43_378 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m43]; exact w42_378
    have w43_37c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m43]; exact w42_37c
    have b43_80 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m43]; exact b42_80
    have b43_94 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m43]; exact b42_94
    clear b42_94 b42_80 w42_37c w42_378 w42_288 w42_284 w42_280 w42_27c w42_260 w42_25c w42_90 w42_8c w42_88 w42_84 w42_7c w42_78 g42_10 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_9 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', tl28', h5', h6', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; rw [hr28] at h5'; cases h5'; rw [hr41] at h6'; cases h6'), sv_fail F E43 s43 t43 (fun x hx => (fR43 x hx).trans (fM x hx).symm) V43 hret g43_2 g43_18 hO g43_3 g43_4⟩
  · rw [hr41] at R41
    obtain ⟨a0_41, a1_41⟩ := R41
    have g41_10 : reg n41 a0 = BitVec.ofNat 32 0x0 := a0_41
    have g41_11 : reg n41 a1 = BitVec.ofNat 32 0x0 := by rw [a1_41]; rfl
    have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := keep_kk40.trans K41
    clear keep_kk40
    have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K41.w32 (by decide) (by decide)).trans w40_78
    have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K41.w32 (by decide) (by decide)).trans w40_7c
    have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K41.w32 (by decide) (by decide)).trans w40_84
    have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := (K41.w32 (by decide) (by decide)).trans w40_88
    have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := (K41.w32 (by decide) (by decide)).trans w40_8c
    have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := (K41.w32 (by decide) (by decide)).trans w40_90
    have w41_25c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K41.w32 (by decide) (by decide)).trans w40_25c
    have w41_260 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := (K41.w32 (by decide) (by decide)).trans w40_260
    have w41_27c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K41.w32 (by decide) (by decide)).trans w40_27c
    have w41_280 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K41.w32 (by decide) (by decide)).trans w40_280
    have w41_284 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := (K41.w32 (by decide) (by decide)).trans w40_284
    have w41_288 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := (K41.w32 (by decide) (by decide)).trans w40_288
    have w41_378 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K41.w32 (by decide) (by decide)).trans w40_378
    have w41_37c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K41.w32 (by decide) (by decide)).trans w40_37c
    have b41_80 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := (K41.b8 (by decide) (by decide)).trans b40_80
    have b41_94 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := (K41.b8 (by decide) (by decide)).trans b40_94
    clear b40_94 b40_80 w40_37c w40_378 w40_288 w40_284 w40_280 w40_27c w40_268 w40_264 w40_260 w40_25c w40_90 w40_8c w40_88 w40_84 w40_7c w40_78 g40_11 g40_10 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_12 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
    -- 0x134
    obtain ⟨n42, c42, u42⟩ := s41.block svL2134 E41.self svL2134_end
      ⟨trivial, trivial, trivial⟩
    have m42 : n42.mem = n41.mem := u42.mem
    have s42 : St n42.mem SV n42 0x138 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
    have rb42 : ∀ q, reg n42 q = (runBlock svL2134 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
    have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
    have t42 : Steps n0 n42 := t41.trans c42
    have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
    have E42 : SvCode n42.mem := E41.fr F fr42
    have V42 : SvSaves B n42.mem v := V41.same m42
    have g42_2 : reg n42 sp = B + 0x21A0 := by
      rw [rb42, runBlock_reg _ _ _ sp s41.zero (by decide), g41_2]
    have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb42, runBlock_reg _ _ _ (3 : Fin 32) s41.zero (by decide), g41_3]
    have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb42, runBlock_reg _ _ _ (4 : Fin 32) s41.zero (by decide), g41_4]
    have g42_9 : reg n42 (9 : Fin 32) = cp := by
      rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
    have g42_11 : reg n42 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb42, runBlock_reg _ _ _ a1 s41.zero (by decide), g41_11]
    have g42_18 : reg n42 (18 : Fin 32) = out := by
      rw [rb42, runBlock_reg _ _ _ (18 : Fin 32) s41.zero (by decide), g41_18]
    have g42_19 : reg n42 (19 : Fin 32) = bp := by
      rw [rb42, runBlock_reg _ _ _ (19 : Fin 32) s41.zero (by decide), g41_19]
    have g42_20 : reg n42 (20 : Fin 32) = dg := by
      rw [rb42, runBlock_reg _ _ _ (20 : Fin 32) s41.zero (by decide), g41_20]
    have g42_21 : reg n42 (21 : Fin 32) = rootp := by
      rw [rb42, runBlock_reg _ _ _ (21 : Fin 32) s41.zero (by decide), g41_21]
    have g42_22 : reg n42 (22 : Fin 32) = ll := by
      rw [rb42, runBlock_reg _ _ _ (22 : Fin 32) s41.zero (by decide), g41_22]
    have g42_23 : reg n42 (23 : Fin 32) = bp16 := by
      rw [rb42, runBlock_reg _ _ _ (23 : Fin 32) s41.zero (by decide), g41_23]
    have g42_24 : reg n42 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
      rw [rb42, runBlock_reg _ _ _ (24 : Fin 32) s41.zero (by decide), g41_24]
    have g42_25 : reg n42 (25 : Fin 32) = bl16 := by
      rw [rb42, runBlock_reg _ _ _ (25 : Fin 32) s41.zero (by decide), g41_25]
    have g42_26 : reg n42 (26 : Fin 32) = lp := by
      rw [rb42, runBlock_reg _ _ _ (26 : Fin 32) s41.zero (by decide), g41_26]
    have g42_27 : reg n42 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb42, runBlock_reg _ _ _ (27 : Fin 32) s41.zero (by decide), g41_27]
    have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb42]; simp +decide only [runBlock, BInstr.run, svL2134, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g42_10 : reg n42 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb42]; simp +decide only [runBlock, BInstr.run, svL2134, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m42]; exact keep_kk41
    clear keep_kk41
    have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m42]; exact w41_78
    have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m42]; exact w41_7c
    have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m42]; exact w41_84
    have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m42]; exact w41_88
    have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m42]; exact w41_8c
    have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m42]; exact w41_90
    have w42_25c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m42]; exact w41_25c
    have w42_260 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m42]; exact w41_260
    have w42_27c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m42]; exact w41_27c
    have w42_280 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m42]; exact w41_280
    have w42_284 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m42]; exact w41_284
    have w42_288 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m42]; exact w41_288
    have w42_378 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m42]; exact w41_378
    have w42_37c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m42]; exact w41_37c
    have b42_80 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m42]; exact b41_80
    have b42_94 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m42]; exact b41_94
    clear b41_94 b41_80 w41_37c w41_378 w41_288 w41_284 w41_280 w41_27c w41_260 w41_25c w41_90 w41_8c w41_88 w41_84 w41_7c w41_78 g41_11 g41_10 a1_41 a0_41
    -- 0x138: branch, not taken
    obtain ⟨n43, d43, u43⟩ := s42.notTaken E42.self 0x13C sv_at_138
      (by decide) (by rw [g42_10, s42.zero]; decide)
    have s43 : St n43.mem SV n43 0x13C (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
    have m43 : n43.mem = n42.mem := u43.mem
    have fr43 : ∀ x, SvR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
    have t43 : Steps n0 n43 := t42.trans (.single d43)
    have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
    have E43 : SvCode n43.mem := E42.fr F fr43
    have V43 : SvSaves B n43.mem v := V42.same m43
    have g43_2 : reg n43 sp = B + 0x21A0 := by rw [u43.regs, g42_2]
    have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u43.regs, g42_3]
    have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u43.regs, g42_4]
    have g43_8 : reg n43 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u43.regs, g42_8]
    have g43_9 : reg n43 (9 : Fin 32) = cp := by rw [u43.regs, g42_9]
    have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x0 := by rw [u43.regs, g42_10]
    have g43_11 : reg n43 a1 = BitVec.ofNat 32 0x0 := by rw [u43.regs, g42_11]
    have g43_18 : reg n43 (18 : Fin 32) = out := by rw [u43.regs, g42_18]
    have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [u43.regs, g42_19]
    have g43_20 : reg n43 (20 : Fin 32) = dg := by rw [u43.regs, g42_20]
    have g43_21 : reg n43 (21 : Fin 32) = rootp := by rw [u43.regs, g42_21]
    have g43_22 : reg n43 (22 : Fin 32) = ll := by rw [u43.regs, g42_22]
    have g43_23 : reg n43 (23 : Fin 32) = bp16 := by rw [u43.regs, g42_23]
    have g43_24 : reg n43 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u43.regs, g42_24]
    have g43_25 : reg n43 (25 : Fin 32) = bl16 := by rw [u43.regs, g42_25]
    have g43_26 : reg n43 (26 : Fin 32) = lp := by rw [u43.regs, g42_26]
    have g43_27 : reg n43 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u43.regs, g42_27]
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m43]; exact keep_kk42
    clear keep_kk42
    have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m43]; exact w42_78
    have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m43]; exact w42_7c
    have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m43]; exact w42_84
    have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m43]; exact w42_88
    have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m43]; exact w42_8c
    have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m43]; exact w42_90
    have w43_25c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m43]; exact w42_25c
    have w43_260 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m43]; exact w42_260
    have w43_27c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m43]; exact w42_27c
    have w43_280 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m43]; exact w42_280
    have w43_284 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m43]; exact w42_284
    have w43_288 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m43]; exact w42_288
    have w43_378 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m43]; exact w42_378
    have w43_37c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m43]; exact w42_37c
    have b43_80 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m43]; exact b42_80
    have b43_94 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m43]; exact b42_94
    clear b42_94 b42_80 w42_37c w42_378 w42_288 w42_284 w42_280 w42_27c w42_260 w42_25c w42_90 w42_8c w42_88 w42_84 w42_7c w42_78 g42_10 g42_8 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_11 g42_9 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    -- 0x13C
    obtain ⟨n44, c44, u44⟩ := s43.block svL213c E43.self svL213c_end
      ⟨trivial, trivial, trivial⟩
    have m44 : n44.mem = n43.mem := u44.mem
    have s44 : St n44.mem SV n44 0x142 (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
    have rb44 : ∀ q, reg n44 q = (runBlock svL213c (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
    have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
    have t44 : Steps n0 n44 := t43.trans c44
    have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
    have E44 : SvCode n44.mem := E43.fr F fr44
    have V44 : SvSaves B n44.mem v := V43.same m44
    have g44_2 : reg n44 sp = B + 0x21A0 := by
      rw [rb44, runBlock_reg _ _ _ sp s43.zero (by decide), g43_2]
    have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb44, runBlock_reg _ _ _ (3 : Fin 32) s43.zero (by decide), g43_3]
    have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb44, runBlock_reg _ _ _ (4 : Fin 32) s43.zero (by decide), g43_4]
    have g44_9 : reg n44 (9 : Fin 32) = cp := by
      rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
    have g44_11 : reg n44 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb44, runBlock_reg _ _ _ a1 s43.zero (by decide), g43_11]
    have g44_18 : reg n44 (18 : Fin 32) = out := by
      rw [rb44, runBlock_reg _ _ _ (18 : Fin 32) s43.zero (by decide), g43_18]
    have g44_19 : reg n44 (19 : Fin 32) = bp := by
      rw [rb44, runBlock_reg _ _ _ (19 : Fin 32) s43.zero (by decide), g43_19]
    have g44_20 : reg n44 (20 : Fin 32) = dg := by
      rw [rb44, runBlock_reg _ _ _ (20 : Fin 32) s43.zero (by decide), g43_20]
    have g44_21 : reg n44 (21 : Fin 32) = rootp := by
      rw [rb44, runBlock_reg _ _ _ (21 : Fin 32) s43.zero (by decide), g43_21]
    have g44_22 : reg n44 (22 : Fin 32) = ll := by
      rw [rb44, runBlock_reg _ _ _ (22 : Fin 32) s43.zero (by decide), g43_22]
    have g44_23 : reg n44 (23 : Fin 32) = bp16 := by
      rw [rb44, runBlock_reg _ _ _ (23 : Fin 32) s43.zero (by decide), g43_23]
    have g44_24 : reg n44 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
      rw [rb44, runBlock_reg _ _ _ (24 : Fin 32) s43.zero (by decide), g43_24]
    have g44_25 : reg n44 (25 : Fin 32) = bl16 := by
      rw [rb44, runBlock_reg _ _ _ (25 : Fin 32) s43.zero (by decide), g43_25]
    have g44_26 : reg n44 (26 : Fin 32) = lp := by
      rw [rb44, runBlock_reg _ _ _ (26 : Fin 32) s43.zero (by decide), g43_26]
    have g44_27 : reg n44 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb44, runBlock_reg _ _ _ (27 : Fin 32) s43.zero (by decide), g43_27]
    have g44_8 : reg n44 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb44]; simp +decide only [runBlock, BInstr.run, svL213c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb44]; simp +decide only [runBlock, BInstr.run, svL213c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m44]; exact keep_kk43
    clear keep_kk43
    have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m44]; exact w43_78
    have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m44]; exact w43_7c
    have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m44]; exact w43_84
    have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m44]; exact w43_88
    have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m44]; exact w43_8c
    have w44_90 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m44]; exact w43_90
    have w44_25c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m44]; exact w43_25c
    have w44_260 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m44]; exact w43_260
    have w44_27c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m44]; exact w43_27c
    have w44_280 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m44]; exact w43_280
    have w44_284 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m44]; exact w43_284
    have w44_288 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m44]; exact w43_288
    have w44_378 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m44]; exact w43_378
    have w44_37c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m44]; exact w43_37c
    have b44_80 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m44]; exact b43_80
    have b44_94 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m44]; exact b43_94
    clear b43_94 b43_80 w43_37c w43_378 w43_288 w43_284 w43_280 w43_27c w43_260 w43_25c w43_90 w43_8c w43_88 w43_84 w43_7c w43_78 g43_27 g43_26 g43_25 g43_24 g43_23 g43_22 g43_21 g43_20 g43_19 g43_18 g43_11 g43_10 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 m43 s43 u43 d43
    -- 0x142: branch, taken
    obtain ⟨n45, d45, u45⟩ := s44.taken E44.self 0x7A4 sv_at_142
      (by decide) (by rw [g44_10, s44.zero]; decide)
    have s45 : St n45.mem SV n45 0x7A4 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
    have m45 : n45.mem = n44.mem := u45.mem
    have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
    have t45 : Steps n0 n45 := t44.trans (.single d45)
    have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
    have E45 : SvCode n45.mem := E44.fr F fr45
    have V45 : SvSaves B n45.mem v := V44.same m45
    have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, g44_2]
    have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, g44_3]
    have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, g44_4]
    have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u45.regs, g44_8]
    have g45_9 : reg n45 (9 : Fin 32) = cp := by rw [u45.regs, g44_9]
    have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x0 := by rw [u45.regs, g44_10]
    have g45_11 : reg n45 a1 = BitVec.ofNat 32 0x0 := by rw [u45.regs, g44_11]
    have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
    have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
    have g45_20 : reg n45 (20 : Fin 32) = dg := by rw [u45.regs, g44_20]
    have g45_21 : reg n45 (21 : Fin 32) = rootp := by rw [u45.regs, g44_21]
    have g45_22 : reg n45 (22 : Fin 32) = ll := by rw [u45.regs, g44_22]
    have g45_23 : reg n45 (23 : Fin 32) = bp16 := by rw [u45.regs, g44_23]
    have g45_24 : reg n45 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u45.regs, g44_24]
    have g45_25 : reg n45 (25 : Fin 32) = bl16 := by rw [u45.regs, g44_25]
    have g45_26 : reg n45 (26 : Fin 32) = lp := by rw [u45.regs, g44_26]
    have g45_27 : reg n45 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u45.regs, g44_27]
    have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m45]; exact keep_kk44
    clear keep_kk44
    have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m45]; exact w44_78
    have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m45]; exact w44_7c
    have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m45]; exact w44_84
    have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m45]; exact w44_88
    have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m45]; exact w44_8c
    have w45_90 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m45]; exact w44_90
    have w45_25c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m45]; exact w44_25c
    have w45_260 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m45]; exact w44_260
    have w45_27c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m45]; exact w44_27c
    have w45_280 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m45]; exact w44_280
    have w45_284 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m45]; exact w44_284
    have w45_288 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m45]; exact w44_288
    have w45_378 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m45]; exact w44_378
    have w45_37c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m45]; exact w44_37c
    have b45_80 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m45]; exact b44_80
    have b45_94 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m45]; exact b44_94
    clear b44_94 b44_80 w44_37c w44_378 w44_288 w44_284 w44_280 w44_27c w44_260 w44_25c w44_90 w44_8c w44_88 w44_84 w44_7c w44_78 g44_10 g44_8 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_11 g44_9 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', tl28', h5', h6', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; rw [hr28] at h5'; cases h5'; rw [hr41] at h6'; cases h6'), sv_fail F E45 s45 t45 (fun x hx => (fR45 x hx).trans (fM x hx).symm) V45 hret g45_2 g45_18 hO g45_3 g45_4⟩
  obtain ⟨te41, hte41⟩ := ii_ok_elem hr41
  obtain ⟨d8_41, d12_41⟩ := A41 te41 hte41
  rw [hr41] at R41
  obtain ⟨a0_41, a1_41⟩ := R41
  have g41_10 : reg n41 a0 = BitVec.ofNat 32 0x0 := a0_41
  have g41_11 : reg n41 a1 = BitVec.ofNat 32 0x1 := by rw [a1_41]; rfl
  have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := keep_kk40.trans K41
  clear keep_kk40
  have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K41.w32 (by decide) (by decide)).trans w40_78
  have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K41.w32 (by decide) (by decide)).trans w40_7c
  have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K41.w32 (by decide) (by decide)).trans w40_84
  have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := (K41.w32 (by decide) (by decide)).trans w40_88
  have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := (K41.w32 (by decide) (by decide)).trans w40_8c
  have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := (K41.w32 (by decide) (by decide)).trans w40_90
  have w41_25c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := (K41.w32 (by decide) (by decide)).trans w40_25c
  have w41_260 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := (K41.w32 (by decide) (by decide)).trans w40_260
  have w41_27c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := (K41.w32 (by decide) (by decide)).trans w40_27c
  have w41_280 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := (K41.w32 (by decide) (by decide)).trans w40_280
  have w41_284 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := (K41.w32 (by decide) (by decide)).trans w40_284
  have w41_288 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := (K41.w32 (by decide) (by decide)).trans w40_288
  have w41_378 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K41.w32 (by decide) (by decide)).trans w40_378
  have w41_37c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K41.w32 (by decide) (by decide)).trans w40_37c
  have b41_80 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := (K41.b8 (by decide) (by decide)).trans b40_80
  have b41_94 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := (K41.b8 (by decide) (by decide)).trans b40_94
  have w41_264 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) + BitVec.ofNat 32 (te41.header + te41.len) := d8_41
  have w41_268 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := d12_41
  clear b40_94 b40_80 w40_37c w40_378 w40_288 w40_284 w40_280 w40_27c w40_268 w40_264 w40_260 w40_25c w40_90 w40_8c w40_88 w40_84 w40_7c w40_78 g40_11 g40_10 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_12 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
  -- 0x134
  obtain ⟨n42, c42, u42⟩ := s41.block svL2134 E41.self svL2134_end
    ⟨trivial, trivial, trivial⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have s42 : St n42.mem SV n42 0x138 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have rb42 : ∀ q, reg n42 q = (runBlock svL2134 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
  have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
  have t42 : Steps n0 n42 := t41.trans c42
  have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
  have E42 : SvCode n42.mem := E41.fr F fr42
  have V42 : SvSaves B n42.mem v := V41.same m42
  have g42_2 : reg n42 sp = B + 0x21A0 := by
    rw [rb42, runBlock_reg _ _ _ sp s41.zero (by decide), g41_2]
  have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb42, runBlock_reg _ _ _ (3 : Fin 32) s41.zero (by decide), g41_3]
  have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb42, runBlock_reg _ _ _ (4 : Fin 32) s41.zero (by decide), g41_4]
  have g42_9 : reg n42 (9 : Fin 32) = cp := by
    rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
  have g42_11 : reg n42 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb42, runBlock_reg _ _ _ a1 s41.zero (by decide), g41_11]
  have g42_18 : reg n42 (18 : Fin 32) = out := by
    rw [rb42, runBlock_reg _ _ _ (18 : Fin 32) s41.zero (by decide), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by
    rw [rb42, runBlock_reg _ _ _ (19 : Fin 32) s41.zero (by decide), g41_19]
  have g42_20 : reg n42 (20 : Fin 32) = dg := by
    rw [rb42, runBlock_reg _ _ _ (20 : Fin 32) s41.zero (by decide), g41_20]
  have g42_21 : reg n42 (21 : Fin 32) = rootp := by
    rw [rb42, runBlock_reg _ _ _ (21 : Fin 32) s41.zero (by decide), g41_21]
  have g42_22 : reg n42 (22 : Fin 32) = ll := by
    rw [rb42, runBlock_reg _ _ _ (22 : Fin 32) s41.zero (by decide), g41_22]
  have g42_23 : reg n42 (23 : Fin 32) = bp16 := by
    rw [rb42, runBlock_reg _ _ _ (23 : Fin 32) s41.zero (by decide), g41_23]
  have g42_24 : reg n42 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb42, runBlock_reg _ _ _ (24 : Fin 32) s41.zero (by decide), g41_24]
  have g42_25 : reg n42 (25 : Fin 32) = bl16 := by
    rw [rb42, runBlock_reg _ _ _ (25 : Fin 32) s41.zero (by decide), g41_25]
  have g42_26 : reg n42 (26 : Fin 32) = lp := by
    rw [rb42, runBlock_reg _ _ _ (26 : Fin 32) s41.zero (by decide), g41_26]
  have g42_27 : reg n42 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb42, runBlock_reg _ _ _ (27 : Fin 32) s41.zero (by decide), g41_27]
  have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svL2134, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g42_10 : reg n42 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svL2134, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m42]; exact keep_kk41
  clear keep_kk41
  have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m42]; exact w41_78
  have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m42]; exact w41_7c
  have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m42]; exact w41_84
  have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m42]; exact w41_88
  have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m42]; exact w41_8c
  have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m42]; exact w41_90
  have w42_25c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m42]; exact w41_25c
  have w42_260 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m42]; exact w41_260
  have w42_264 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) + BitVec.ofNat 32 (te41.header + te41.len) := by rw [m42]; exact w41_264
  have w42_268 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [m42]; exact w41_268
  have w42_27c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m42]; exact w41_27c
  have w42_280 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m42]; exact w41_280
  have w42_284 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m42]; exact w41_284
  have w42_288 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m42]; exact w41_288
  have w42_378 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m42]; exact w41_378
  have w42_37c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m42]; exact w41_37c
  have b42_80 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m42]; exact b41_80
  have b42_94 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m42]; exact b41_94
  clear w41_268 w41_264 b41_94 b41_80 w41_37c w41_378 w41_288 w41_284 w41_280 w41_27c w41_260 w41_25c w41_90 w41_8c w41_88 w41_84 w41_7c w41_78 g41_11 g41_10 a1_41 a0_41 d12_41 d8_41 g41_2 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_9 g41_8 g41_4 g41_3 V41 E41 fR41 t41 fr41 A41 K41 rk41 sp41 s41 c41
  -- 0x138: branch, not taken
  obtain ⟨n43, d43, u43⟩ := s42.notTaken E42.self 0x13C sv_at_138
    (by decide) (by rw [g42_10, s42.zero]; decide)
  have s43 : St n43.mem SV n43 0x13C (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
  have m43 : n43.mem = n42.mem := u43.mem
  have fr43 : ∀ x, SvR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
  have t43 : Steps n0 n43 := t42.trans (.single d43)
  have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.same m43
  have g43_2 : reg n43 sp = B + 0x21A0 := by rw [u43.regs, g42_2]
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u43.regs, g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u43.regs, g42_4]
  have g43_8 : reg n43 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u43.regs, g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = cp := by rw [u43.regs, g42_9]
  have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x0 := by rw [u43.regs, g42_10]
  have g43_11 : reg n43 a1 = BitVec.ofNat 32 0x1 := by rw [u43.regs, g42_11]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [u43.regs, g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [u43.regs, g42_19]
  have g43_20 : reg n43 (20 : Fin 32) = dg := by rw [u43.regs, g42_20]
  have g43_21 : reg n43 (21 : Fin 32) = rootp := by rw [u43.regs, g42_21]
  have g43_22 : reg n43 (22 : Fin 32) = ll := by rw [u43.regs, g42_22]
  have g43_23 : reg n43 (23 : Fin 32) = bp16 := by rw [u43.regs, g42_23]
  have g43_24 : reg n43 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u43.regs, g42_24]
  have g43_25 : reg n43 (25 : Fin 32) = bl16 := by rw [u43.regs, g42_25]
  have g43_26 : reg n43 (26 : Fin 32) = lp := by rw [u43.regs, g42_26]
  have g43_27 : reg n43 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u43.regs, g42_27]
  have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m43]; exact keep_kk42
  clear keep_kk42
  have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m43]; exact w42_78
  have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m43]; exact w42_7c
  have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m43]; exact w42_84
  have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m43]; exact w42_88
  have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m43]; exact w42_8c
  have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m43]; exact w42_90
  have w43_25c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m43]; exact w42_25c
  have w43_260 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m43]; exact w42_260
  have w43_264 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) + BitVec.ofNat 32 (te41.header + te41.len) := by rw [m43]; exact w42_264
  have w43_268 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [m43]; exact w42_268
  have w43_27c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m43]; exact w42_27c
  have w43_280 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m43]; exact w42_280
  have w43_284 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m43]; exact w42_284
  have w43_288 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m43]; exact w42_288
  have w43_378 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m43]; exact w42_378
  have w43_37c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m43]; exact w42_37c
  have b43_80 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m43]; exact b42_80
  have b43_94 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m43]; exact b42_94
  clear b42_94 b42_80 w42_37c w42_378 w42_288 w42_284 w42_280 w42_27c w42_268 w42_264 w42_260 w42_25c w42_90 w42_8c w42_88 w42_84 w42_7c w42_78 g42_10 g42_8 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_11 g42_9 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
  -- 0x13C
  obtain ⟨n44, c44, u44⟩ := s43.block svL213c E43.self svL213c_end
    ⟨trivial, trivial, trivial⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have s44 : St n44.mem SV n44 0x142 (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have rb44 : ∀ q, reg n44 q = (runBlock svL213c (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
  have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
  have t44 : Steps n0 n44 := t43.trans c44
  have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
  have E44 : SvCode n44.mem := E43.fr F fr44
  have V44 : SvSaves B n44.mem v := V43.same m44
  have g44_2 : reg n44 sp = B + 0x21A0 := by
    rw [rb44, runBlock_reg _ _ _ sp s43.zero (by decide), g43_2]
  have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb44, runBlock_reg _ _ _ (3 : Fin 32) s43.zero (by decide), g43_3]
  have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb44, runBlock_reg _ _ _ (4 : Fin 32) s43.zero (by decide), g43_4]
  have g44_9 : reg n44 (9 : Fin 32) = cp := by
    rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
  have g44_11 : reg n44 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb44, runBlock_reg _ _ _ a1 s43.zero (by decide), g43_11]
  have g44_18 : reg n44 (18 : Fin 32) = out := by
    rw [rb44, runBlock_reg _ _ _ (18 : Fin 32) s43.zero (by decide), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = bp := by
    rw [rb44, runBlock_reg _ _ _ (19 : Fin 32) s43.zero (by decide), g43_19]
  have g44_20 : reg n44 (20 : Fin 32) = dg := by
    rw [rb44, runBlock_reg _ _ _ (20 : Fin 32) s43.zero (by decide), g43_20]
  have g44_21 : reg n44 (21 : Fin 32) = rootp := by
    rw [rb44, runBlock_reg _ _ _ (21 : Fin 32) s43.zero (by decide), g43_21]
  have g44_22 : reg n44 (22 : Fin 32) = ll := by
    rw [rb44, runBlock_reg _ _ _ (22 : Fin 32) s43.zero (by decide), g43_22]
  have g44_23 : reg n44 (23 : Fin 32) = bp16 := by
    rw [rb44, runBlock_reg _ _ _ (23 : Fin 32) s43.zero (by decide), g43_23]
  have g44_24 : reg n44 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb44, runBlock_reg _ _ _ (24 : Fin 32) s43.zero (by decide), g43_24]
  have g44_25 : reg n44 (25 : Fin 32) = bl16 := by
    rw [rb44, runBlock_reg _ _ _ (25 : Fin 32) s43.zero (by decide), g43_25]
  have g44_26 : reg n44 (26 : Fin 32) = lp := by
    rw [rb44, runBlock_reg _ _ _ (26 : Fin 32) s43.zero (by decide), g43_26]
  have g44_27 : reg n44 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb44, runBlock_reg _ _ _ (27 : Fin 32) s43.zero (by decide), g43_27]
  have g44_8 : reg n44 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svL213c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svL213c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m44]; exact keep_kk43
  clear keep_kk43
  have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m44]; exact w43_78
  have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m44]; exact w43_7c
  have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m44]; exact w43_84
  have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m44]; exact w43_88
  have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m44]; exact w43_8c
  have w44_90 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m44]; exact w43_90
  have w44_25c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m44]; exact w43_25c
  have w44_260 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m44]; exact w43_260
  have w44_264 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) + BitVec.ofNat 32 (te41.header + te41.len) := by rw [m44]; exact w43_264
  have w44_268 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [m44]; exact w43_268
  have w44_27c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m44]; exact w43_27c
  have w44_280 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m44]; exact w43_280
  have w44_284 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m44]; exact w43_284
  have w44_288 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m44]; exact w43_288
  have w44_378 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m44]; exact w43_378
  have w44_37c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m44]; exact w43_37c
  have b44_80 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m44]; exact b43_80
  have b44_94 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m44]; exact b43_94
  clear b43_94 b43_80 w43_37c w43_378 w43_288 w43_284 w43_280 w43_27c w43_268 w43_264 w43_260 w43_25c w43_90 w43_8c w43_88 w43_84 w43_7c w43_78 g43_27 g43_26 g43_25 g43_24 g43_23 g43_22 g43_21 g43_20 g43_19 g43_18 g43_11 g43_10 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 m43 s43 u43 d43
  -- 0x142: branch, not taken
  obtain ⟨n45, d45, u45⟩ := s44.notTaken E44.self 0x146 sv_at_142
    (by decide) (by rw [g44_10, s44.zero]; decide)
  have s45 : St n45.mem SV n45 0x146 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
  have m45 : n45.mem = n44.mem := u45.mem
  have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
  have t45 : Steps n0 n45 := t44.trans (.single d45)
  have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.same m45
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, g44_4]
  have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u45.regs, g44_8]
  have g45_9 : reg n45 (9 : Fin 32) = cp := by rw [u45.regs, g44_9]
  have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_10]
  have g45_11 : reg n45 a1 = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_11]
  have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
  have g45_20 : reg n45 (20 : Fin 32) = dg := by rw [u45.regs, g44_20]
  have g45_21 : reg n45 (21 : Fin 32) = rootp := by rw [u45.regs, g44_21]
  have g45_22 : reg n45 (22 : Fin 32) = ll := by rw [u45.regs, g44_22]
  have g45_23 : reg n45 (23 : Fin 32) = bp16 := by rw [u45.regs, g44_23]
  have g45_24 : reg n45 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u45.regs, g44_24]
  have g45_25 : reg n45 (25 : Fin 32) = bl16 := by rw [u45.regs, g44_25]
  have g45_26 : reg n45 (26 : Fin 32) = lp := by rw [u45.regs, g44_26]
  have g45_27 : reg n45 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u45.regs, g44_27]
  have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m45]; exact keep_kk44
  clear keep_kk44
  have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m45]; exact w44_78
  have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m45]; exact w44_7c
  have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m45]; exact w44_84
  have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m45]; exact w44_88
  have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m45]; exact w44_8c
  have w45_90 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m45]; exact w44_90
  have w45_25c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m45]; exact w44_25c
  have w45_260 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m45]; exact w44_260
  have w45_264 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) + BitVec.ofNat 32 (te41.header + te41.len) := by rw [m45]; exact w44_264
  have w45_268 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [m45]; exact w44_268
  have w45_27c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m45]; exact w44_27c
  have w45_280 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m45]; exact w44_280
  have w45_284 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m45]; exact w44_284
  have w45_288 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m45]; exact w44_288
  have w45_378 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m45]; exact w44_378
  have w45_37c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m45]; exact w44_37c
  have b45_80 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m45]; exact b44_80
  have b45_94 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m45]; exact b44_94
  clear b44_94 b44_80 w44_37c w44_378 w44_288 w44_284 w44_280 w44_27c w44_268 w44_264 w44_260 w44_25c w44_90 w44_8c w44_88 w44_84 w44_7c w44_78 g44_10 g44_8 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_11 g44_9 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
  -- 0x146: lw
  obtain ⟨n46, d46, u46⟩ := s45.lw E45.self sv_at_146 (off' := 0x14A) (by decide)
    (by rw [g45_2, show B + 0x21A0 + 0x268 = B + 0x21A0 + BitVec.ofNat 32 0x268 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s46 : St n46.mem SV n46 0x14A (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
  have m46 : n46.mem = n45.mem := u46.mem
  have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
  have t46 : Steps n0 n46 := t45.trans (.single d46)
  have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.same m46
  have g46_2 : reg n46 sp = B + 0x21A0 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_4]
  have g46_8 : reg n46 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_8]
  have g46_9 : reg n46 (9 : Fin 32) = cp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_9]
  have g46_11 : reg n46 a1 = BitVec.ofNat 32 0x1 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_11]
  have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, upd_ne (by decide) (by decide), g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_19]
  have g46_20 : reg n46 (20 : Fin 32) = dg := by rw [u46.regs, upd_ne (by decide) (by decide), g45_20]
  have g46_21 : reg n46 (21 : Fin 32) = rootp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = ll := by rw [u46.regs, upd_ne (by decide) (by decide), g45_22]
  have g46_23 : reg n46 (23 : Fin 32) = bp16 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_23]
  have g46_24 : reg n46 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u46.regs, upd_ne (by decide) (by decide), g45_24]
  have g46_25 : reg n46 (25 : Fin 32) = bl16 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_25]
  have g46_26 : reg n46 (26 : Fin 32) = lp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_26]
  have g46_27 : reg n46 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_27]
  have g46_10 : reg n46 a0 = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by
    rw [u46.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g45_2, show B + 0x21A0 + 0x268 = B + 0x21A0 + BitVec.ofNat 32 0x268 by sv_addr, w45_268]
  have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m46]; exact keep_kk45
  clear keep_kk45
  have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m46]; exact w45_78
  have w46_7c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m46]; exact w45_7c
  have w46_84 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m46]; exact w45_84
  have w46_88 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m46]; exact w45_88
  have w46_8c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m46]; exact w45_8c
  have w46_90 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m46]; exact w45_90
  have w46_25c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m46]; exact w45_25c
  have w46_260 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m46]; exact w45_260
  have w46_264 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) + BitVec.ofNat 32 (te41.header + te41.len) := by rw [m46]; exact w45_264
  have w46_268 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [m46]; exact w45_268
  have w46_27c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m46]; exact w45_27c
  have w46_280 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m46]; exact w45_280
  have w46_284 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m46]; exact w45_284
  have w46_288 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m46]; exact w45_288
  have w46_378 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m46]; exact w45_378
  have w46_37c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m46]; exact w45_37c
  have b46_80 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m46]; exact b45_80
  have b46_94 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m46]; exact b45_94
  clear b45_94 b45_80 w45_37c w45_378 w45_288 w45_284 w45_280 w45_27c w45_268 w45_264 w45_260 w45_25c w45_90 w45_8c w45_88 w45_84 w45_7c w45_78 g45_27 g45_26 g45_25 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_11 g45_10 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45
  by_cases hz_46 : (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) = 0
  rotate_left
  · -- 0x14A: branch, not taken
    obtain ⟨n47, d47, u47⟩ := s46.notTaken E46.self 0x14C sv_at_14a
      (by decide) (by rw [g46_10, s46.zero]; exact br_beq_f hz_46)
    have s47 : St n47.mem SV n47 0x14C (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
    have m47 : n47.mem = n46.mem := u47.mem
    have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
    have t47 : Steps n0 n47 := t46.trans (.single d47)
    have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
    have E47 : SvCode n47.mem := E46.fr F fr47
    have V47 : SvSaves B n47.mem v := V46.same m47
    have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
    have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
    have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
    have g47_8 : reg n47 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u47.regs, g46_8]
    have g47_9 : reg n47 (9 : Fin 32) = cp := by rw [u47.regs, g46_9]
    have g47_10 : reg n47 a0 = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [u47.regs, g46_10]
    have g47_11 : reg n47 a1 = BitVec.ofNat 32 0x1 := by rw [u47.regs, g46_11]
    have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
    have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
    have g47_20 : reg n47 (20 : Fin 32) = dg := by rw [u47.regs, g46_20]
    have g47_21 : reg n47 (21 : Fin 32) = rootp := by rw [u47.regs, g46_21]
    have g47_22 : reg n47 (22 : Fin 32) = ll := by rw [u47.regs, g46_22]
    have g47_23 : reg n47 (23 : Fin 32) = bp16 := by rw [u47.regs, g46_23]
    have g47_24 : reg n47 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u47.regs, g46_24]
    have g47_25 : reg n47 (25 : Fin 32) = bl16 := by rw [u47.regs, g46_25]
    have g47_26 : reg n47 (26 : Fin 32) = lp := by rw [u47.regs, g46_26]
    have g47_27 : reg n47 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u47.regs, g46_27]
    have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m47]; exact keep_kk46
    clear keep_kk46
    have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m47]; exact w46_78
    have w47_7c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m47]; exact w46_7c
    have w47_84 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m47]; exact w46_84
    have w47_88 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m47]; exact w46_88
    have w47_8c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m47]; exact w46_8c
    have w47_90 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m47]; exact w46_90
    have w47_25c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m47]; exact w46_25c
    have w47_260 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m47]; exact w46_260
    have w47_264 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) + BitVec.ofNat 32 (te41.header + te41.len) := by rw [m47]; exact w46_264
    have w47_268 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [m47]; exact w46_268
    have w47_27c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m47]; exact w46_27c
    have w47_280 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m47]; exact w46_280
    have w47_284 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m47]; exact w46_284
    have w47_288 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m47]; exact w46_288
    have w47_378 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m47]; exact w46_378
    have w47_37c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m47]; exact w46_37c
    have b47_80 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m47]; exact b46_80
    have b47_94 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m47]; exact b46_94
    clear b46_94 b46_80 w46_37c w46_378 w46_288 w46_284 w46_280 w46_27c w46_268 w46_264 w46_260 w46_25c w46_90 w46_8c w46_88 w46_84 w46_7c w46_78 g46_10 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_11 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
    -- 0x14C
    obtain ⟨n48, c48, u48⟩ := s47.block svL214c E47.self svL214c_end
      ⟨trivial, trivial⟩
    have m48 : n48.mem = n47.mem := u48.mem
    have s48 : St n48.mem SV n48 0x14E (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
    have rb48 : ∀ q, reg n48 q = (runBlock svL214c (n47.mem, reg n47)).2 q := fun q => by rw [u48.regs]
    have fr48 : ∀ x, SvR B x → n48.mem x = n47.mem x := fun x _ => by rw [m48]
    have t48 : Steps n0 n48 := t47.trans c48
    have fR48 : ∀ x, SvR B x → n48.mem x = M0 x := fun x hx => (fr48 x hx).trans (fR47 x hx)
    have E48 : SvCode n48.mem := E47.fr F fr48
    have V48 : SvSaves B n48.mem v := V47.same m48
    have g48_2 : reg n48 sp = B + 0x21A0 := by
      rw [rb48, runBlock_reg _ _ _ sp s47.zero (by decide), g47_2]
    have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb48, runBlock_reg _ _ _ (3 : Fin 32) s47.zero (by decide), g47_3]
    have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb48, runBlock_reg _ _ _ (4 : Fin 32) s47.zero (by decide), g47_4]
    have g48_9 : reg n48 (9 : Fin 32) = cp := by
      rw [rb48, runBlock_reg _ _ _ (9 : Fin 32) s47.zero (by decide), g47_9]
    have g48_10 : reg n48 a0 = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by
      rw [rb48, runBlock_reg _ _ _ a0 s47.zero (by decide), g47_10]
    have g48_11 : reg n48 a1 = BitVec.ofNat 32 0x1 := by
      rw [rb48, runBlock_reg _ _ _ a1 s47.zero (by decide), g47_11]
    have g48_18 : reg n48 (18 : Fin 32) = out := by
      rw [rb48, runBlock_reg _ _ _ (18 : Fin 32) s47.zero (by decide), g47_18]
    have g48_19 : reg n48 (19 : Fin 32) = bp := by
      rw [rb48, runBlock_reg _ _ _ (19 : Fin 32) s47.zero (by decide), g47_19]
    have g48_20 : reg n48 (20 : Fin 32) = dg := by
      rw [rb48, runBlock_reg _ _ _ (20 : Fin 32) s47.zero (by decide), g47_20]
    have g48_21 : reg n48 (21 : Fin 32) = rootp := by
      rw [rb48, runBlock_reg _ _ _ (21 : Fin 32) s47.zero (by decide), g47_21]
    have g48_22 : reg n48 (22 : Fin 32) = ll := by
      rw [rb48, runBlock_reg _ _ _ (22 : Fin 32) s47.zero (by decide), g47_22]
    have g48_23 : reg n48 (23 : Fin 32) = bp16 := by
      rw [rb48, runBlock_reg _ _ _ (23 : Fin 32) s47.zero (by decide), g47_23]
    have g48_24 : reg n48 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
      rw [rb48, runBlock_reg _ _ _ (24 : Fin 32) s47.zero (by decide), g47_24]
    have g48_25 : reg n48 (25 : Fin 32) = bl16 := by
      rw [rb48, runBlock_reg _ _ _ (25 : Fin 32) s47.zero (by decide), g47_25]
    have g48_26 : reg n48 (26 : Fin 32) = lp := by
      rw [rb48, runBlock_reg _ _ _ (26 : Fin 32) s47.zero (by decide), g47_26]
    have g48_27 : reg n48 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb48, runBlock_reg _ _ _ (27 : Fin 32) s47.zero (by decide), g47_27]
    have g48_8 : reg n48 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb48]; simp +decide only [runBlock, BInstr.run, svL214c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g47_2, g47_3, g47_4, g47_8, g47_9, g47_10, g47_11, g47_18, g47_19, g47_20, g47_21, g47_22, g47_23, g47_24, g47_25, g47_26, g47_27, s47.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m48]; exact keep_kk47
    clear keep_kk47
    have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m48]; exact w47_78
    have w48_7c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m48]; exact w47_7c
    have w48_84 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m48]; exact w47_84
    have w48_88 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m48]; exact w47_88
    have w48_8c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m48]; exact w47_8c
    have w48_90 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m48]; exact w47_90
    have w48_25c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m48]; exact w47_25c
    have w48_260 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m48]; exact w47_260
    have w48_264 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) + BitVec.ofNat 32 (te41.header + te41.len) := by rw [m48]; exact w47_264
    have w48_268 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [m48]; exact w47_268
    have w48_27c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m48]; exact w47_27c
    have w48_280 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m48]; exact w47_280
    have w48_284 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m48]; exact w47_284
    have w48_288 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m48]; exact w47_288
    have w48_378 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m48]; exact w47_378
    have w48_37c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m48]; exact w47_37c
    have b48_80 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m48]; exact b47_80
    have b48_94 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m48]; exact b47_94
    clear b47_94 b47_80 w47_37c w47_378 w47_288 w47_284 w47_280 w47_27c w47_268 w47_264 w47_260 w47_25c w47_90 w47_8c w47_88 w47_84 w47_7c w47_78 g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_11 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
    -- 0x14E: j
    obtain ⟨n49, d49, u49⟩ := s48.jump E48.self sv_at_14e (off' := 0x7A4) (by decide)
      (by rw [s48.pc]; decide)
    have s49 : St n49.mem SV n49 0x7A4 (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
    have m49 : n49.mem = n48.mem := u49.mem
    have fr49 : ∀ x, SvR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
    have t49 : Steps n0 n49 := t48.trans (.single d49)
    have fR49 : ∀ x, SvR B x → n49.mem x = M0 x := fun x hx => (fr49 x hx).trans (fR48 x hx)
    have E49 : SvCode n49.mem := E48.fr F fr49
    have V49 : SvSaves B n49.mem v := V48.same m49
    have g49_2 : reg n49 sp = B + 0x21A0 := by rw [u49.regs, g48_2]
    have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u49.regs, g48_3]
    have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u49.regs, g48_4]
    have g49_8 : reg n49 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u49.regs, g48_8]
    have g49_9 : reg n49 (9 : Fin 32) = cp := by rw [u49.regs, g48_9]
    have g49_10 : reg n49 a0 = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [u49.regs, g48_10]
    have g49_11 : reg n49 a1 = BitVec.ofNat 32 0x1 := by rw [u49.regs, g48_11]
    have g49_18 : reg n49 (18 : Fin 32) = out := by rw [u49.regs, g48_18]
    have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [u49.regs, g48_19]
    have g49_20 : reg n49 (20 : Fin 32) = dg := by rw [u49.regs, g48_20]
    have g49_21 : reg n49 (21 : Fin 32) = rootp := by rw [u49.regs, g48_21]
    have g49_22 : reg n49 (22 : Fin 32) = ll := by rw [u49.regs, g48_22]
    have g49_23 : reg n49 (23 : Fin 32) = bp16 := by rw [u49.regs, g48_23]
    have g49_24 : reg n49 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u49.regs, g48_24]
    have g49_25 : reg n49 (25 : Fin 32) = bl16 := by rw [u49.regs, g48_25]
    have g49_26 : reg n49 (26 : Fin 32) = lp := by rw [u49.regs, g48_26]
    have g49_27 : reg n49 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u49.regs, g48_27]
    have keep_kk49 : SvKeepL B n0.mem n49.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m49]; exact keep_kk48
    clear keep_kk48
    have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m49]; exact w48_78
    have w49_7c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m49]; exact w48_7c
    have w49_84 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m49]; exact w48_84
    have w49_88 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m49]; exact w48_88
    have w49_8c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m49]; exact w48_8c
    have w49_90 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m49]; exact w48_90
    have w49_25c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m49]; exact w48_25c
    have w49_260 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m49]; exact w48_260
    have w49_264 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) + BitVec.ofNat 32 (te41.header + te41.len) := by rw [m49]; exact w48_264
    have w49_268 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [m49]; exact w48_268
    have w49_27c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m49]; exact w48_27c
    have w49_280 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m49]; exact w48_280
    have w49_284 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m49]; exact w48_284
    have w49_288 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m49]; exact w48_288
    have w49_378 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m49]; exact w48_378
    have w49_37c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m49]; exact w48_37c
    have b49_80 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m49]; exact b48_80
    have b49_94 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m49]; exact b48_94
    clear b48_94 b48_80 w48_37c w48_378 w48_288 w48_284 w48_280 w48_27c w48_268 w48_264 w48_260 w48_25c w48_90 w48_8c w48_88 w48_84 w48_7c w48_78 g48_8 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_11 g48_10 g48_9 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 rb48 s48 m48 u48 c48
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', tl28', h5', h6', te41', h7', h8', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; rw [hr28] at h5'; cases h5'; rw [hr41] at h6'; cases h6'; rw [hte41] at h7'; cases h7'; exact hz_46 h8'), sv_fail F E49 s49 t49 (fun x hx => (fR49 x hx).trans (fM x hx).symm) V49 hret g49_2 g49_18 hO g49_3 g49_4⟩
  -- 0x14A: branch, taken
  obtain ⟨n47, d47, u47⟩ := s46.taken E46.self 0x154 sv_at_14a
    (by decide) (by rw [g46_10, s46.zero]; exact br_beq_t hz_46)
  have s47 : St n47.mem SV n47 0x154 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
  have m47 : n47.mem = n46.mem := u47.mem
  have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
  have t47 : Steps n0 n47 := t46.trans (.single d47)
  have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : SvCode n47.mem := E46.fr F fr47
  have V47 : SvSaves B n47.mem v := V46.same m47
  have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
  have g47_8 : reg n47 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u47.regs, g46_8]
  have g47_9 : reg n47 (9 : Fin 32) = cp := by rw [u47.regs, g46_9]
  have g47_10 : reg n47 a0 = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [u47.regs, g46_10]
  have g47_11 : reg n47 a1 = BitVec.ofNat 32 0x1 := by rw [u47.regs, g46_11]
  have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
  have g47_20 : reg n47 (20 : Fin 32) = dg := by rw [u47.regs, g46_20]
  have g47_21 : reg n47 (21 : Fin 32) = rootp := by rw [u47.regs, g46_21]
  have g47_22 : reg n47 (22 : Fin 32) = ll := by rw [u47.regs, g46_22]
  have g47_23 : reg n47 (23 : Fin 32) = bp16 := by rw [u47.regs, g46_23]
  have g47_24 : reg n47 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u47.regs, g46_24]
  have g47_25 : reg n47 (25 : Fin 32) = bl16 := by rw [u47.regs, g46_25]
  have g47_26 : reg n47 (26 : Fin 32) = lp := by rw [u47.regs, g46_26]
  have g47_27 : reg n47 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u47.regs, g46_27]
  have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m47]; exact keep_kk46
  clear keep_kk46
  have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m47]; exact w46_78
  have w47_7c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m47]; exact w46_7c
  have w47_84 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m47]; exact w46_84
  have w47_88 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m47]; exact w46_88
  have w47_8c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m47]; exact w46_8c
  have w47_90 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m47]; exact w46_90
  have w47_25c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m47]; exact w46_25c
  have w47_260 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m47]; exact w46_260
  have w47_264 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) + BitVec.ofNat 32 (te41.header + te41.len) := by rw [m47]; exact w46_264
  have w47_268 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [m47]; exact w46_268
  have w47_27c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m47]; exact w46_27c
  have w47_280 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m47]; exact w46_280
  have w47_284 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m47]; exact w46_284
  have w47_288 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m47]; exact w46_288
  have w47_378 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m47]; exact w46_378
  have w47_37c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m47]; exact w46_37c
  have b47_80 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m47]; exact b46_80
  have b47_94 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m47]; exact b46_94
  clear b46_94 b46_80 w46_37c w46_378 w46_288 w46_284 w46_280 w46_27c w46_268 w46_264 w46_260 w46_25c w46_90 w46_8c w46_88 w46_84 w46_7c w46_78 g46_10 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_11 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
  -- 0x154
  obtain ⟨n48, c48, u48⟩ := s47.block svL2154 E47.self svL2154_end
    ⟨trivial, trivial, trivial⟩
  have m48 : n48.mem = n47.mem := u48.mem
  have s48 : St n48.mem SV n48 0x158 (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
  have rb48 : ∀ q, reg n48 q = (runBlock svL2154 (n47.mem, reg n47)).2 q := fun q => by rw [u48.regs]
  have fr48 : ∀ x, SvR B x → n48.mem x = n47.mem x := fun x _ => by rw [m48]
  have t48 : Steps n0 n48 := t47.trans c48
  have fR48 : ∀ x, SvR B x → n48.mem x = M0 x := fun x hx => (fr48 x hx).trans (fR47 x hx)
  have E48 : SvCode n48.mem := E47.fr F fr48
  have V48 : SvSaves B n48.mem v := V47.same m48
  have g48_2 : reg n48 sp = B + 0x21A0 := by
    rw [rb48, runBlock_reg _ _ _ sp s47.zero (by decide), g47_2]
  have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb48, runBlock_reg _ _ _ (3 : Fin 32) s47.zero (by decide), g47_3]
  have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb48, runBlock_reg _ _ _ (4 : Fin 32) s47.zero (by decide), g47_4]
  have g48_8 : reg n48 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb48, runBlock_reg _ _ _ (8 : Fin 32) s47.zero (by decide), g47_8]
  have g48_9 : reg n48 (9 : Fin 32) = cp := by
    rw [rb48, runBlock_reg _ _ _ (9 : Fin 32) s47.zero (by decide), g47_9]
  have g48_18 : reg n48 (18 : Fin 32) = out := by
    rw [rb48, runBlock_reg _ _ _ (18 : Fin 32) s47.zero (by decide), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by
    rw [rb48, runBlock_reg _ _ _ (19 : Fin 32) s47.zero (by decide), g47_19]
  have g48_20 : reg n48 (20 : Fin 32) = dg := by
    rw [rb48, runBlock_reg _ _ _ (20 : Fin 32) s47.zero (by decide), g47_20]
  have g48_21 : reg n48 (21 : Fin 32) = rootp := by
    rw [rb48, runBlock_reg _ _ _ (21 : Fin 32) s47.zero (by decide), g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = ll := by
    rw [rb48, runBlock_reg _ _ _ (22 : Fin 32) s47.zero (by decide), g47_22]
  have g48_23 : reg n48 (23 : Fin 32) = bp16 := by
    rw [rb48, runBlock_reg _ _ _ (23 : Fin 32) s47.zero (by decide), g47_23]
  have g48_24 : reg n48 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb48, runBlock_reg _ _ _ (24 : Fin 32) s47.zero (by decide), g47_24]
  have g48_25 : reg n48 (25 : Fin 32) = bl16 := by
    rw [rb48, runBlock_reg _ _ _ (25 : Fin 32) s47.zero (by decide), g47_25]
  have g48_26 : reg n48 (26 : Fin 32) = lp := by
    rw [rb48, runBlock_reg _ _ _ (26 : Fin 32) s47.zero (by decide), g47_26]
  have g48_27 : reg n48 (27 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb48, runBlock_reg _ _ _ (27 : Fin 32) s47.zero (by decide), g47_27]
  have g48_10 : reg n48 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb48]; simp +decide only [runBlock, BInstr.run, svL2154, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g47_2, g47_3, g47_4, g47_8, g47_9, g47_10, g47_11, g47_18, g47_19, g47_20, g47_21, g47_22, g47_23, g47_24, g47_25, g47_26, g47_27, s47.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g48_11 : reg n48 a1 = B + 0x21A0 + BitVec.ofNat 32 0x27C := by
    rw [rb48]; simp +decide only [runBlock, BInstr.run, svL2154, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g47_2, g47_3, g47_4, g47_8, g47_9, g47_10, g47_11, g47_18, g47_19, g47_20, g47_21, g47_22, g47_23, g47_24, g47_25, g47_26, g47_27, s47.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8)] := by rw [m48]; exact keep_kk47
  clear keep_kk47
  have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m48]; exact w47_78
  have w48_7c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m48]; exact w47_7c
  have w48_84 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m48]; exact w47_84
  have w48_88 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 tl28.len := by rw [m48]; exact w47_88
  have w48_8c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m48]; exact w47_8c
  have w48_90 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m48]; exact w47_90
  have w48_25c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header := by rw [m48]; exact w47_25c
  have w48_260 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl28.len := by rw [m48]; exact w47_260
  have w48_264 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl28.header) + BitVec.ofNat 32 (te41.header + te41.len) := by rw [m48]; exact w47_264
  have w48_268 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl28.len) - BitVec.ofNat 32 (te41.header + te41.len) := by rw [m48]; exact w47_268
  have w48_27c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m48]; exact w47_27c
  have w48_280 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1.len := by rw [m48]; exact w47_280
  have w48_284 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m48]; exact w47_284
  have w48_288 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl28.header + tl28.len) := by rw [m48]; exact w47_288
  have w48_378 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m48]; exact w47_378
  have w48_37c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m48]; exact w47_37c
  have b48_80 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m48]; exact b47_80
  have b48_94 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 8 tl28.tag := by rw [m48]; exact b47_94
  clear b47_94 b47_80 w47_37c w47_378 w47_288 w47_284 w47_280 w47_27c w47_268 w47_264 w47_260 w47_25c w47_90 w47_8c w47_88 w47_84 w47_7c w47_78 g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_11 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
  exact .inr ⟨tl1, hr1, tl8, hr8, tl16, hr16, bp16, bl16, hr16b, hz_19, tl28, hr28, hr41, te41, hte41, hz_46, n48, t48, s48, E48, V48, fR48, g48_2, g48_3, g48_4, g48_8, g48_9, g48_10, g48_11, g48_18, g48_19, g48_20, g48_21, g48_22, g48_23, g48_24, g48_25, g48_26, g48_27, w48_78, w48_7c, w48_27c, w48_280, w48_284, w48_288, keep_kk48.mono (by decide)⟩

end C3.RV32.Sv
