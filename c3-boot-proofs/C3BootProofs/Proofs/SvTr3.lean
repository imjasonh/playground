import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: the `SignedData`'s digest algorithms and content type

From 0xC08 to 0xCC4: the digest algorithms are a `SET` that holds SHA-256 and nothing else, and the encapsulated content is a `SEQUENCE` whose type is TSTInfo.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTr3c08 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x320]
theorem svTr3c08_end : blockEnd sigstoreVerifyCode 0xC08 svTr3c08 = some 0xC0E := by
  simp only [svTr3c08]
  rw [blockEnd, sv_at_c08]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_c0c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr3c22 : List BInstr :=
  [.aluImm .add a1 sp 0x425, .aluImm .add a0 sp 0x335, .aluImm .add a2 x0 0xB]
theorem svTr3c22_end : blockEnd sigstoreVerifyCode 0xC22 svTr3c22 = some 0xC2C := by
  simp only [svTr3c22]
  rw [blockEnd, sv_at_c22]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_c26]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_c2a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr3c3c : List BInstr :=
  [.aluImm .add a0 sp 0x330]
theorem svTr3c3c_end : blockEnd sigstoreVerifyCode 0xC3C svTr3c3c = some 0xC3E := by
  simp only [svTr3c3c]
  rw [blockEnd, sv_at_c3c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr3c46 : List BInstr :=
  [.aluImm .and a0 a0 0x1, .alu .add (8 : Fin 32) x0 a1]
theorem svTr3c46_end : blockEnd sigstoreVerifyCode 0xC46 svTr3c46 = some 0xC4A := by
  simp only [svTr3c46]
  rw [blockEnd, sv_at_c46]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_c48]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr3c4e : List BInstr :=
  [.aluImm .and a0 (8 : Fin 32) 0x1, .aluImm .add (8 : Fin 32) x0 0x18]
theorem svTr3c4e_end : blockEnd sigstoreVerifyCode 0xC4E svTr3c4e = some 0xC54 := by
  simp only [svTr3c4e]
  rw [blockEnd, sv_at_c4e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_c52]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr3c60 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x320]
theorem svTr3c60_end : blockEnd sigstoreVerifyCode 0xC60 svTr3c60 = some 0xC66 := by
  simp only [svTr3c60]
  rw [blockEnd, sv_at_c60]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_c64]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr3c7a : List BInstr :=
  [.aluImm .add a1 sp 0x425, .aluImm .add a0 sp 0x345, .aluImm .add a2 x0 0xB]
theorem svTr3c7a_end : blockEnd sigstoreVerifyCode 0xC7A svTr3c7a = some 0xC84 := by
  simp only [svTr3c7a]
  rw [blockEnd, sv_at_c7a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_c7e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_c82]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr3c94 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x340]
theorem svTr3c94_end : blockEnd sigstoreVerifyCode 0xC94 svTr3c94 = some 0xC9A := by
  simp only [svTr3c94]
  rw [blockEnd, sv_at_c94]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_c98]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr3cae : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF84A, .aluImm .add a3 x0 0xB]
theorem svTr3cae_end : blockEnd sigstoreVerifyCode 0xCAE svTr3cae = some 0xCB8 := by
  simp only [svTr3cae]
  rw [blockEnd, sv_at_cae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_cb2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_cb6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr312b8 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x18]
theorem svTr312b8_end : blockEnd sigstoreVerifyCode 0x12B8 svTr312b8 = some 0x12BA := by
  simp only [svTr312b8]
  rw [blockEnd, sv_at_12b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tr3 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 sdp sdl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xC08 (reg n0))
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
    (w0_328 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp)
    (w0_32c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl)
    (sd_in : SvIn B (sdp) (sdl).toNat)
    (D0 : SvData M0) :
    (¬ (∃ tl2, derElement 0x31 (memBytes M0 (sdp) (sdl).toNat) = .ok tl2 ∧ isSha256Of M0 ((sdp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat = .ok true ∧ ∃ te11, derElement 0x30 (memBytes M0 ((sdp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat) = .ok te11 ∧ ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) = 0) ∧ ∃ tl19, derElement 0x30 (memBytes M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = .ok tl19 ∧ ∃ op28 ol28, derContent (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) (derOid (memBytes M0 (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) (BitVec.ofNat 32 tl19.len).toNat)) = .ok (op28, ol28) ∧ ∃ to28, derOid (memBytes M0 (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) (BitVec.ofNat 32 tl19.len).toNat) = .ok to28 ∧ (memBytes M0 op28 ol28.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl2, derElement 0x31 (memBytes M0 (sdp) (sdl).toNat) = .ok tl2 ∧
    isSha256Of M0 ((sdp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat = .ok true ∧
    ∃ te11, derElement 0x30 (memBytes M0 ((sdp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat) = .ok te11 ∧
    ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) = 0) ∧
    ∃ tl19, derElement 0x30 (memBytes M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = .ok tl19 ∧
    ∃ op28 ol28, derContent (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) (derOid (memBytes M0 (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) (BitVec.ofNat 32 tl19.len).toNat)) = .ok (op28, ol28) ∧
    ∃ to28, derOid (memBytes M0 (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) (BitVec.ofNat 32 tl19.len).toNat) = .ok to28 ∧
    (memBytes M0 op28 ol28.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xCC4 (reg n') ∧
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
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) + BitVec.ofNat 32 (to28.header + to28.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (BitVec.ofNat 32 tl19.len) - BitVec.ofNat 32 (to28.header + to28.len) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xC08
  obtain ⟨n1, c1, u1⟩ := s0.block svTr3c08 E0.self svTr3c08_end
    ⟨trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0xC0E (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTr3c08 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans c1
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by
    rw [rb1, runBlock_reg _ _ _ sp s0.zero (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb1, runBlock_reg _ _ _ (3 : Fin 32) s0.zero (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb1, runBlock_reg _ _ _ (4 : Fin 32) s0.zero (by decide), g0_4]
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = x24 := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = x27 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr3c08, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr3c08, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_328 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m1]; exact w0_328
  have w1_32c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m1]; exact w0_32c
  -- 0xC0E: sv_setF
  obtain ⟨n2, c2, s2, sp2, rk2, K2, Ok2, Er2, fr2⟩ := sv_setF (oc := 0x420) (dc := 0x320)
    F E1 s1 sv_at_c0e sv_at_c12 (by decide) (by decide) g1_2 g1_10 g1_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w1_328 w1_32c sd_in
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keepL K2 (by decide)
  rw [sv_mb fR1 sd_in] at Ok2 Er2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rk2 sp (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk2 (3 : Fin 32) (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk2 (4 : Fin 32) (by decide) (by decide), g1_4]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [rk2 (18 : Fin 32) (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [rk2 (19 : Fin 32) (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [rk2 (20 : Fin 32) (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [rk2 (21 : Fin 32) (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [rk2 (22 : Fin 32) (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [rk2 (23 : Fin 32) (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by rw [rk2 (24 : Fin 32) (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [rk2 (25 : Fin 32) (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [rk2 (26 : Fin 32) (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = x27 := by rw [rk2 (27 : Fin 32) (by decide) (by decide), g1_27]
  obtain ⟨r2, hr2⟩ : ∃ r, derElement 0x31 (memBytes M0 (sdp) (sdl).toNat) = r := ⟨_, rfl⟩
  rcases r2 with er2 | tl2
  · obtain ⟨z2, -⟩ := Er2 er2 hr2
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x10), (0x328, 0x8)] := keep_kk1.trans K2
    clear keep_kk1
    have w2_420 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z2
    clear w1_32c w1_328 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0xC16: lw
    obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_c16 (off' := 0xC1A) (by decide)
      (by rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s3 : St n3.mem SV n3 0xC1A (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
    have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
    have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
    have g3_9 : reg n3 (9 : Fin 32) = 0 := by
      rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w2_420]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x10), (0x328, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_420 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m3]; exact w2_420
    clear w2_420 z2
    -- 0xC1A: lbu
    obtain ⟨n4, d4, u4⟩ := s3.lbu E3.self sv_at_c1a (off' := 0xC1E) (by decide)
    have s4 : St n4.mem SV n4 0xC1E (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
    have g4_9 : reg n4 (9 : Fin 32) = 0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_9]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
    have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
    have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
    have g4_24 : reg n4 (24 : Fin 32) = x24 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_24]
    have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = x27 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x10), (0x328, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m4]; exact w3_420
    clear w3_420 g3_9 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    -- 0xC1E: branch, taken
    obtain ⟨n5, d5, u5⟩ := s4.taken E4.self 0x7A4 sv_at_c1e
      (by decide) (by rw [g4_9, s4.zero]; rfl)
    have s5 : St n5.mem SV n5 0x7A4 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
    have g5_9 : reg n5 (9 : Fin 32) = 0 := by rw [u5.regs, g4_9]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
    have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, g4_20]
    have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, g4_22]
    have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, g4_23]
    have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [u5.regs, g4_24]
    have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [u5.regs, g4_27]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x10), (0x328, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m5]; exact w4_420
    clear w4_420 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    exact .inl ⟨(fun ⟨tl2', h0', _⟩ => by rw [hr2] at h0'; cases h0'), sv_fail F E5 s5 t5 (fun x hx => (fR5 x hx).trans (fM x hx).symm) V5 hret g5_2 g5_18 hO g5_3 g5_4⟩
  obtain ⟨o0_2, o4_2, o8_2, o12_2, d8_2, d12_2⟩ := Ok2 tl2 hr2
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x10), (0x328, 0x8)] := keep_kk1.trans K2
  clear keep_kk1
  have w2_328 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := d8_2
  have w2_32c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := d12_2
  have w2_420 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := o0_2
  have w2_424 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := o4_2
  have w2_428 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := o8_2
  have w2_42c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := o12_2
  clear w1_32c w1_328 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0xC16: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_c16 (off' := 0xC1A) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0xC1A (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
  have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_9 : reg n3 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w2_420]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x10), (0x328, 0x8)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_328 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_328
  have w3_32c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_32c
  have w3_420 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m3]; exact w2_420
  have w3_424 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m3]; exact w2_424
  have w3_428 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m3]; exact w2_428
  have w3_42c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m3]; exact w2_42c
  clear w2_42c w2_428 w2_424 w2_420 w2_32c w2_328 d12_2 d8_2 o12_2 o8_2 o4_2 o0_2 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 Er2 Ok2 K2 rk2 sp2 s2 c2
  -- 0xC1A: lbu
  obtain ⟨n4, d4, u4⟩ := s3.lbu E3.self sv_at_c1a (off' := 0xC1E) (by decide)
  have b3_424 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by
    have h := byte_of_ld w3_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s4 : St n4.mem SV n4 0xC1E (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_9 : reg n4 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u4.regs, upd_ne (by decide) (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = x24 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = x27 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
  have g4_8 : reg n4 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b3_424]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x10), (0x328, 0x8)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_328 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_328
  have w4_32c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_32c
  have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m4]; exact w3_420
  have w4_424 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m4]; exact w3_424
  have w4_428 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m4]; exact w3_428
  have w4_42c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m4]; exact w3_42c
  have b4_424 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m4]; exact b3_424
  clear w3_42c w3_428 w3_424 w3_420 w3_32c w3_328 g3_9 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0xC1E: branch, not taken
  obtain ⟨n5, d5, u5⟩ := s4.notTaken E4.self 0xC22 sv_at_c1e
    (by decide) (by rw [g4_9, s4.zero]; exact br_beq_f (sd_in.ok_ne hr2))
  have s5 : St n5.mem SV n5 0xC22 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u5.regs, g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u5.regs, g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [u5.regs, g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [u5.regs, g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x10), (0x328, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_328 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_328
  have w5_32c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_32c
  have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m5]; exact w4_420
  have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m5]; exact w4_424
  have w5_428 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m5]; exact w4_428
  have w5_42c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m5]; exact w4_42c
  have b5_424 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m5]; exact b4_424
  clear b4_424 w4_42c w4_428 w4_424 w4_420 w4_32c w4_328 g4_8 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 b3_424 u4 d4
  -- 0xC22
  obtain ⟨n6, c6, u6⟩ := s5.block svTr3c22 E5.self svTr3c22_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0xC2C (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svTr3c22 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_8 : reg n6 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by
    rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
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
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x335 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTr3c22, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_11 : reg n6 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTr3c22, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_12 : reg n6 a2 = BitVec.ofNat 32 0xB := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTr3c22, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x10), (0x328, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_328
  have w6_32c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_32c
  have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m6]; exact w5_420
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m6]; exact w5_424
  have w6_428 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m6]; exact w5_428
  have w6_42c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m6]; exact w5_42c
  have b6_424 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m6]; exact b5_424
  clear b5_424 w5_42c w5_428 w5_424 w5_420 w5_32c w5_328 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  have b6_425 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by
    have h := byte_of_ld w6_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b6_426 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by
    have h := byte_of_ld w6_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b6_427 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by
    have h := byte_of_ld w6_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0xC2C: memcpy
  obtain ⟨n7, P7, K7, X7⟩ := sv_mc (c := 0x335) (d := 0x425) (N := 0xB) F E6 s6 sv_at_c2c sv_at_c30
    (by decide) (by decide) g6_2 g6_10 g6_11 g6_12
    (by decide) (by decide) (by decide)
  have s7 := P7.st
  have fr7 := P7.fr
  have t7 : Steps n0 n7 := t6.trans P7.steps
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [P7.regs sp (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P7.regs (3 : Fin 32) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P7.regs (4 : Fin 32) (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [P7.regs (8 : Fin 32) (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [P7.regs (9 : Fin 32) (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [P7.regs (18 : Fin 32) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [P7.regs (19 : Fin 32) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [P7.regs (20 : Fin 32) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [P7.regs (21 : Fin 32) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [P7.regs (22 : Fin 32) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [P7.regs (23 : Fin 32) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [P7.regs (24 : Fin 32) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [P7.regs (25 : Fin 32) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [P7.regs (26 : Fin 32) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [P7.regs (27 : Fin 32) (by decide), g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_328 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K7.w32 (by decide) (by decide)).trans w6_328
  have w7_32c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K7.w32 (by decide) (by decide)).trans w6_32c
  have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := (K7.w32 (by decide) (by decide)).trans w6_420
  have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := (K7.w32 (by decide) (by decide)).trans w6_424
  have w7_428 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := (K7.w32 (by decide) (by decide)).trans w6_428
  have w7_42c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K7.w32 (by decide) (by decide)).trans w6_42c
  have b7_424 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K7.b8 (by decide) (by decide)).trans b6_424
  have b7_425 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K7.b8 (by decide) (by decide)).trans b6_425
  have b7_426 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K7.b8 (by decide) (by decide)).trans b6_426
  have b7_427 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K7.b8 (by decide) (by decide)).trans b6_427
  have w7_338 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = (sdp) + BitVec.ofNat 32 tl2.header := by
    rw [← w6_428]
    exact ld_cp fun q hq => by
      have := X7 (0x3 + q) (by omega)
      rwa [show 0x335 + (0x3 + q) = 0x338 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w7_33c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = BitVec.ofNat 32 tl2.len := by
    rw [← w6_42c]
    exact ld_cp fun q hq => by
      have := X7 (0x7 + q) (by omega)
      rwa [show 0x335 + (0x7 + q) = 0x33C + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b7_335 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x335) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [show 0x335 = 0x335 + 0x0 from rfl, X7 0x0 (by decide)]; exact b6_425
  have b7_336 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x336) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [show 0x336 = 0x335 + 0x1 from rfl, X7 0x1 (by decide)]; exact b6_426
  have b7_337 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x337) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [show 0x337 = 0x335 + 0x2 from rfl, X7 0x2 (by decide)]; exact b6_427
  clear b6_424 w6_42c w6_428 w6_424 w6_420 w6_32c w6_328 g6_12 g6_11 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0xC34: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_c34 (off' := 0xC38) (c := 0x330)
    (by decide) (by rw [g7_2]; sv_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg8 (8 : Fin 32), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [rg8 (9 : Fin 32), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [rg8 (20 : Fin 32), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [rg8 (22 : Fin 32), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [rg8 (23 : Fin 32), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [rg8 (26 : Fin 32), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by rw [rg8 (27 : Fin 32), g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_328 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K8.w32 (by decide) (by decide)).trans w7_328
  have w8_32c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K8.w32 (by decide) (by decide)).trans w7_32c
  have w8_338 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = (sdp) + BitVec.ofNat 32 tl2.header := (K8.w32 (by decide) (by decide)).trans w7_338
  have w8_33c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = BitVec.ofNat 32 tl2.len := (K8.w32 (by decide) (by decide)).trans w7_33c
  have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := (K8.w32 (by decide) (by decide)).trans w7_420
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := (K8.w32 (by decide) (by decide)).trans w7_424
  have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := (K8.w32 (by decide) (by decide)).trans w7_428
  have w8_42c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K8.w32 (by decide) (by decide)).trans w7_42c
  have b8_335 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x335) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K8.b8 (by decide) (by decide)).trans b7_335
  have b8_336 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x336) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K8.b8 (by decide) (by decide)).trans b7_336
  have b8_337 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x337) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K8.b8 (by decide) (by decide)).trans b7_337
  have b8_424 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K8.b8 (by decide) (by decide)).trans b7_424
  have b8_425 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K8.b8 (by decide) (by decide)).trans b7_425
  have b8_426 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K8.b8 (by decide) (by decide)).trans b7_426
  have b8_427 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K8.b8 (by decide) (by decide)).trans b7_427
  have w8_330 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [W8, g7_9]
  clear b7_337 b7_336 b7_335 w7_33c w7_338 b7_427 b7_426 b7_425 b7_424 w7_42c w7_428 w7_424 w7_420 w7_32c w7_328 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 s7 X7 K7 P7 b6_427 b6_426 b6_425
  -- 0xC38: sb
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sb F E8 s8 sv_at_c38 (off' := 0xC3C) (c := 0x334)
    (by decide) (by rw [g8_2]; sv_addr) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg9 (8 : Fin 32), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [rg9 (9 : Fin 32), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rg9 (18 : Fin 32), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rg9 (19 : Fin 32), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [rg9 (20 : Fin 32), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [rg9 (21 : Fin 32), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [rg9 (22 : Fin 32), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [rg9 (23 : Fin 32), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [rg9 (24 : Fin 32), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [rg9 (25 : Fin 32), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [rg9 (26 : Fin 32), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [rg9 (27 : Fin 32), g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have w9_328 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K9.w32 (by decide) (by decide)).trans w8_328
  have w9_32c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K9.w32 (by decide) (by decide)).trans w8_32c
  have w9_330 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K9.w32 (by decide) (by decide)).trans w8_330
  have w9_338 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = (sdp) + BitVec.ofNat 32 tl2.header := (K9.w32 (by decide) (by decide)).trans w8_338
  have w9_33c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = BitVec.ofNat 32 tl2.len := (K9.w32 (by decide) (by decide)).trans w8_33c
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := (K9.w32 (by decide) (by decide)).trans w8_420
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := (K9.w32 (by decide) (by decide)).trans w8_424
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := (K9.w32 (by decide) (by decide)).trans w8_428
  have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K9.w32 (by decide) (by decide)).trans w8_42c
  have b9_335 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x335) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K9.b8 (by decide) (by decide)).trans b8_335
  have b9_336 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x336) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K9.b8 (by decide) (by decide)).trans b8_336
  have b9_337 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x337) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K9.b8 (by decide) (by decide)).trans b8_337
  have b9_424 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K9.b8 (by decide) (by decide)).trans b8_424
  have b9_425 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K9.b8 (by decide) (by decide)).trans b8_425
  have b9_426 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K9.b8 (by decide) (by decide)).trans b8_426
  have b9_427 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K9.b8 (by decide) (by decide)).trans b8_427
  have b9_334 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [W9, g8_8, lbu_low]
  clear w8_330 b8_427 b8_426 b8_425 b8_424 b8_337 b8_336 b8_335 w8_42c w8_428 w8_424 w8_420 w8_33c w8_338 w8_32c w8_328 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  have w9_334 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := ld_of_bytes b9_334
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x334 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x335 by sv_addr]; exact b9_335)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x334 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x336 by sv_addr]; exact b9_336)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x334 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x337 by sv_addr]; exact b9_337)
  -- 0xC3C
  obtain ⟨n10, c10, u10⟩ := s9.block svTr3c3c E9.self svTr3c3c_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0xC3E (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svTr3c3c (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_8 : reg n10 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by
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
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x330 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svTr3c3c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_328 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_328
  have w10_32c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_32c
  have w10_330 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m10]; exact w9_330
  have w10_334 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m10]; exact w9_334
  have w10_338 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m10]; exact w9_338
  have w10_33c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = BitVec.ofNat 32 tl2.len := by rw [m10]; exact w9_33c
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m10]; exact w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m10]; exact w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m10]; exact w9_428
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m10]; exact w9_42c
  have b10_424 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m10]; exact b9_424
  have b10_425 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m10]; exact b9_425
  have b10_426 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m10]; exact b9_426
  have b10_427 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m10]; exact b9_427
  clear b9_334 b9_427 b9_426 b9_425 b9_424 b9_337 b9_336 b9_335 w9_42c w9_428 w9_424 w9_420 w9_33c w9_338 w9_330 w9_32c w9_328 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  -- 0xC3E: sv_isShaF
  obtain ⟨n11, c11, s11, sp11, rk11, K11, A11, R11, fr11⟩ := sv_isShaF (dc := 0x330)
    F E10 (D0.sv FW fR10) s10 sv_at_c3e sv_at_c42 (by decide) (by decide) g10_2
    g10_10 (by decide) (by decide) w10_338 w10_33c (sd_in.contentW hr2)
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keepL K11 (by decide)
  rw [isSha256Of_congr (sv_pt fR10 (sd_in.contentW hr2))] at R11
  rw [sv_mb fR10 (sd_in.contentW hr2)] at A11
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk11 (3 : Fin 32) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk11 (4 : Fin 32) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk11 (8 : Fin 32) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [rk11 (9 : Fin 32) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rk11 (18 : Fin 32) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rk11 (19 : Fin 32) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [rk11 (20 : Fin 32) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [rk11 (21 : Fin 32) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [rk11 (22 : Fin 32) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [rk11 (23 : Fin 32) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [rk11 (24 : Fin 32) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [rk11 (25 : Fin 32) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [rk11 (26 : Fin 32) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [rk11 (27 : Fin 32) (by decide), g10_27]
  have g11_2 : reg n11 sp = B + 0x21A0 := sp11
  obtain ⟨r11, hr11⟩ : ∃ r, isSha256Of M0 ((sdp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat = r := ⟨_, rfl⟩
  rcases r11 with b11 | (_ | _)
  · rw [hr11] at R11
    obtain ⟨a0_11, a1_11⟩ := R11
    have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x1 := a0_11
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := keep_kk10.trans K11
    clear keep_kk10
    have w11_328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K11.w32 (by decide) (by decide)).trans w10_328
    have w11_32c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K11.w32 (by decide) (by decide)).trans w10_32c
    have w11_330 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K11.w32 (by decide) (by decide)).trans w10_330
    have w11_334 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := (K11.w32 (by decide) (by decide)).trans w10_334
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := (K11.w32 (by decide) (by decide)).trans w10_420
    have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := (K11.w32 (by decide) (by decide)).trans w10_424
    have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := (K11.w32 (by decide) (by decide)).trans w10_428
    have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K11.w32 (by decide) (by decide)).trans w10_42c
    have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_424
    have b11_425 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K11.b8 (by decide) (by decide)).trans b10_425
    have b11_426 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K11.b8 (by decide) (by decide)).trans b10_426
    have b11_427 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K11.b8 (by decide) (by decide)).trans b10_427
    clear b10_427 b10_426 b10_425 b10_424 w10_42c w10_428 w10_424 w10_420 w10_33c w10_338 w10_334 w10_330 w10_32c w10_328 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10 w9_334
    -- 0xC46
    obtain ⟨n12, c12, u12⟩ := s11.block svTr3c46 E11.self svTr3c46_end
      ⟨trivial, trivial, trivial⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have s12 : St n12.mem SV n12 0xC4A (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have rb12 : ∀ q, reg n12 q = (runBlock svTr3c46 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
    have g12_9 : reg n12 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by
      rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
    have g12_18 : reg n12 (18 : Fin 32) = out := by
      rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by
      rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = x20 := by
      rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by
      rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by
      rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by
      rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = x24 := by
      rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = x25 := by
      rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by
      rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = x27 := by
      rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
    have g12_10 : reg n12 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb12]; simp +decide only [runBlock, BInstr.run, svTr3c46, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_328 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_328
    have w12_32c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_32c
    have w12_330 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_330
    have w12_334 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_334
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_420
    have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_424
    have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_428
    have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_42c
    have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m12]; exact b11_424
    have b12_425 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m12]; exact b11_425
    have b12_426 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m12]; exact b11_426
    have b12_427 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m12]; exact b11_427
    clear b11_427 b11_426 b11_425 b11_424 w11_42c w11_428 w11_424 w11_420 w11_334 w11_330 w11_32c w11_328 g11_10 a1_11 a0_11
    -- 0xC4A: branch, taken
    obtain ⟨n13, d13, u13⟩ := s12.taken E12.self 0x7A4 sv_at_c4a
      (by decide) (by rw [g12_10, s12.zero]; decide)
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
    have g13_9 : reg n13 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u13.regs, g12_9]
    have g13_10 : reg n13 a0 = BitVec.ofNat 32 0x1 := by rw [u13.regs, g12_10]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, g12_27]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m13]; exact w12_328
    have w13_32c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m13]; exact w12_32c
    have w13_330 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_330
    have w13_334 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_334
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_420
    have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_424
    have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_428
    have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_42c
    have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m13]; exact b12_424
    have b13_425 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m13]; exact b12_425
    have b13_426 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m13]; exact b12_426
    have b13_427 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m13]; exact b12_427
    clear b12_427 b12_426 b12_425 b12_424 w12_42c w12_428 w12_424 w12_420 w12_334 w12_330 w12_32c w12_328 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
    exact .inl ⟨(fun ⟨tl2', h0', h1', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr11] at h1'; cases h1'), sv_fail F E13 s13 t13 (fun x hx => (fR13 x hx).trans (fM x hx).symm) V13 hret g13_2 g13_18 hO g13_3 g13_4⟩
  · rw [hr11] at R11
    obtain ⟨a0_11, a1_11⟩ := R11
    have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x0 := a0_11
    have g11_11 : reg n11 a1 = BitVec.ofNat 32 0x0 := by rw [a1_11]; rfl
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := keep_kk10.trans K11
    clear keep_kk10
    have w11_328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K11.w32 (by decide) (by decide)).trans w10_328
    have w11_32c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K11.w32 (by decide) (by decide)).trans w10_32c
    have w11_330 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K11.w32 (by decide) (by decide)).trans w10_330
    have w11_334 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := (K11.w32 (by decide) (by decide)).trans w10_334
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := (K11.w32 (by decide) (by decide)).trans w10_420
    have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := (K11.w32 (by decide) (by decide)).trans w10_424
    have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := (K11.w32 (by decide) (by decide)).trans w10_428
    have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K11.w32 (by decide) (by decide)).trans w10_42c
    have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_424
    have b11_425 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K11.b8 (by decide) (by decide)).trans b10_425
    have b11_426 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K11.b8 (by decide) (by decide)).trans b10_426
    have b11_427 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K11.b8 (by decide) (by decide)).trans b10_427
    clear b10_427 b10_426 b10_425 b10_424 w10_42c w10_428 w10_424 w10_420 w10_33c w10_338 w10_334 w10_330 w10_32c w10_328 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10 w9_334
    -- 0xC46
    obtain ⟨n12, c12, u12⟩ := s11.block svTr3c46 E11.self svTr3c46_end
      ⟨trivial, trivial, trivial⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have s12 : St n12.mem SV n12 0xC4A (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have rb12 : ∀ q, reg n12 q = (runBlock svTr3c46 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
    have g12_9 : reg n12 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by
      rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
    have g12_11 : reg n12 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb12, runBlock_reg _ _ _ a1 s11.zero (by decide), g11_11]
    have g12_18 : reg n12 (18 : Fin 32) = out := by
      rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by
      rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = x20 := by
      rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by
      rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by
      rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by
      rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = x24 := by
      rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = x25 := by
      rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by
      rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = x27 := by
      rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
    have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb12]; simp +decide only [runBlock, BInstr.run, svTr3c46, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_11, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g12_10 : reg n12 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb12]; simp +decide only [runBlock, BInstr.run, svTr3c46, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_11, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_328 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_328
    have w12_32c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_32c
    have w12_330 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_330
    have w12_334 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_334
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_420
    have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_424
    have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_428
    have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_42c
    have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m12]; exact b11_424
    have b12_425 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m12]; exact b11_425
    have b12_426 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m12]; exact b11_426
    have b12_427 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m12]; exact b11_427
    clear b11_427 b11_426 b11_425 b11_424 w11_42c w11_428 w11_424 w11_420 w11_334 w11_330 w11_32c w11_328 g11_11 g11_10 a1_11 a0_11
    -- 0xC4A: branch, not taken
    obtain ⟨n13, d13, u13⟩ := s12.notTaken E12.self 0xC4E sv_at_c4a
      (by decide) (by rw [g12_10, s12.zero]; decide)
    have s13 : St n13.mem SV n13 0xC4E (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
    have t13 : Steps n0 n13 := t12.trans (.single d13)
    have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
    have E13 : SvCode n13.mem := E12.fr F fr13
    have V13 : SvSaves B n13.mem v := V12.same m13
    have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
    have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
    have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
    have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u13.regs, g12_8]
    have g13_9 : reg n13 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u13.regs, g12_9]
    have g13_10 : reg n13 a0 = BitVec.ofNat 32 0x0 := by rw [u13.regs, g12_10]
    have g13_11 : reg n13 a1 = BitVec.ofNat 32 0x0 := by rw [u13.regs, g12_11]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, g12_27]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m13]; exact w12_328
    have w13_32c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m13]; exact w12_32c
    have w13_330 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_330
    have w13_334 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_334
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_420
    have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_424
    have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_428
    have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_42c
    have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m13]; exact b12_424
    have b13_425 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m13]; exact b12_425
    have b13_426 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m13]; exact b12_426
    have b13_427 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m13]; exact b12_427
    clear b12_427 b12_426 b12_425 b12_424 w12_42c w12_428 w12_424 w12_420 w12_334 w12_330 w12_32c w12_328 g12_10 g12_8 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_11 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
    -- 0xC4E
    obtain ⟨n14, c14, u14⟩ := s13.block svTr3c4e E13.self svTr3c4e_end
      ⟨trivial, trivial, trivial⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have s14 : St n14.mem SV n14 0xC54 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have rb14 : ∀ q, reg n14 q = (runBlock svTr3c4e (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
    have g14_9 : reg n14 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by
      rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
    have g14_11 : reg n14 a1 = BitVec.ofNat 32 0x0 := by
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
    have g14_24 : reg n14 (24 : Fin 32) = x24 := by
      rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = x25 := by
      rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = x26 := by
      rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = x27 := by
      rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
    have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb14]; simp +decide only [runBlock, BInstr.run, svTr3c4e, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_11, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g14_10 : reg n14 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb14]; simp +decide only [runBlock, BInstr.run, svTr3c4e, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_11, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m14]; exact keep_kk13
    clear keep_kk13
    have w14_328 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_328
    have w14_32c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_32c
    have w14_330 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_330
    have w14_334 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_334
    have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_420
    have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_424
    have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_428
    have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_42c
    have b14_424 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m14]; exact b13_424
    have b14_425 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m14]; exact b13_425
    have b14_426 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m14]; exact b13_426
    have b14_427 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m14]; exact b13_427
    clear b13_427 b13_426 b13_425 b13_424 w13_42c w13_428 w13_424 w13_420 w13_334 w13_330 w13_32c w13_328 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_11 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
    -- 0xC54: branch, taken
    obtain ⟨n15, d15, u15⟩ := s14.taken E14.self 0x7A4 sv_at_c54
      (by decide) (by rw [g14_10, s14.zero]; decide)
    have s15 : St n15.mem SV n15 0x7A4 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
    have t15 : Steps n0 n15 := t14.trans (.single d15)
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.same m15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
    have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u15.regs, g14_8]
    have g15_9 : reg n15 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u15.regs, g14_9]
    have g15_10 : reg n15 a0 = BitVec.ofNat 32 0x0 := by rw [u15.regs, g14_10]
    have g15_11 : reg n15 a1 = BitVec.ofNat 32 0x0 := by rw [u15.regs, g14_11]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
    have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
    have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, g14_27]
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m15]; exact keep_kk14
    clear keep_kk14
    have w15_328 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_328
    have w15_32c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_32c
    have w15_330 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_330
    have w15_334 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_334
    have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_420
    have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_424
    have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_428
    have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_42c
    have b15_424 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m15]; exact b14_424
    have b15_425 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m15]; exact b14_425
    have b15_426 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m15]; exact b14_426
    have b15_427 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m15]; exact b14_427
    clear b14_427 b14_426 b14_425 b14_424 w14_42c w14_428 w14_424 w14_420 w14_334 w14_330 w14_32c w14_328 g14_10 g14_8 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_11 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
    exact .inl ⟨(fun ⟨tl2', h0', h1', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr11] at h1'; cases h1'), sv_fail F E15 s15 t15 (fun x hx => (fR15 x hx).trans (fM x hx).symm) V15 hret g15_2 g15_18 hO g15_3 g15_4⟩
  obtain ⟨te11, hte11⟩ := isSha256Of_ok_elem hr11
  obtain ⟨d8_11, d12_11⟩ := A11 te11 hte11
  rw [hr11] at R11
  obtain ⟨a0_11, a1_11⟩ := R11
  have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x0 := a0_11
  have g11_11 : reg n11 a1 = BitVec.ofNat 32 0x1 := by rw [a1_11]; rfl
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := keep_kk10.trans K11
  clear keep_kk10
  have w11_328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K11.w32 (by decide) (by decide)).trans w10_328
  have w11_32c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K11.w32 (by decide) (by decide)).trans w10_32c
  have w11_330 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K11.w32 (by decide) (by decide)).trans w10_330
  have w11_334 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := (K11.w32 (by decide) (by decide)).trans w10_334
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := (K11.w32 (by decide) (by decide)).trans w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := (K11.w32 (by decide) (by decide)).trans w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := (K11.w32 (by decide) (by decide)).trans w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K11.w32 (by decide) (by decide)).trans w10_42c
  have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_424
  have b11_425 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K11.b8 (by decide) (by decide)).trans b10_425
  have b11_426 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K11.b8 (by decide) (by decide)).trans b10_426
  have b11_427 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K11.b8 (by decide) (by decide)).trans b10_427
  have w11_338 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := d8_11
  have w11_33c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := d12_11
  clear b10_427 b10_426 b10_425 b10_424 w10_42c w10_428 w10_424 w10_420 w10_33c w10_338 w10_334 w10_330 w10_32c w10_328 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10 w9_334
  -- 0xC46
  obtain ⟨n12, c12, u12⟩ := s11.block svTr3c46 E11.self svTr3c46_end
    ⟨trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0xC4A (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svTr3c46 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_9 : reg n12 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_11 : reg n12 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb12, runBlock_reg _ _ _ a1 s11.zero (by decide), g11_11]
  have g12_18 : reg n12 (18 : Fin 32) = out := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by
    rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by
    rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svTr3c46, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_11, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g12_10 : reg n12 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svTr3c46, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_11, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_328 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_328
  have w12_32c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_32c
  have w12_330 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_330
  have w12_334 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_334
  have w12_338 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m12]; exact w11_338
  have w12_33c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m12]; exact w11_33c
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_42c
  have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m12]; exact b11_424
  have b12_425 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m12]; exact b11_425
  have b12_426 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m12]; exact b11_426
  have b12_427 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m12]; exact b11_427
  clear w11_33c w11_338 b11_427 b11_426 b11_425 b11_424 w11_42c w11_428 w11_424 w11_420 w11_334 w11_330 w11_32c w11_328 g11_11 g11_10 a1_11 a0_11 d12_11 d8_11 g11_2 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 V11 E11 fR11 t11 fr11 A11 K11 rk11 sp11 s11 c11
  -- 0xC4A: branch, not taken
  obtain ⟨n13, d13, u13⟩ := s12.notTaken E12.self 0xC4E sv_at_c4a
    (by decide) (by rw [g12_10, s12.zero]; decide)
  have s13 : St n13.mem SV n13 0xC4E (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u13.regs, g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u13.regs, g12_9]
  have g13_10 : reg n13 a0 = BitVec.ofNat 32 0x0 := by rw [u13.regs, g12_10]
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 0x1 := by rw [u13.regs, g12_11]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [u13.regs, g12_27]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m13]; exact w12_328
  have w13_32c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m13]; exact w12_32c
  have w13_330 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_330
  have w13_334 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_334
  have w13_338 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m13]; exact w12_338
  have w13_33c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m13]; exact w12_33c
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_42c
  have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m13]; exact b12_424
  have b13_425 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m13]; exact b12_425
  have b13_426 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m13]; exact b12_426
  have b13_427 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m13]; exact b12_427
  clear b12_427 b12_426 b12_425 b12_424 w12_42c w12_428 w12_424 w12_420 w12_33c w12_338 w12_334 w12_330 w12_32c w12_328 g12_10 g12_8 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_11 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0xC4E
  obtain ⟨n14, c14, u14⟩ := s13.block svTr3c4e E13.self svTr3c4e_end
    ⟨trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem SV n14 0xC54 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock svTr3c4e (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_9 : reg n14 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 0x1 := by
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
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by
    rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTr3c4e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_11, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTr3c4e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_11, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_328 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_328
  have w14_32c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_32c
  have w14_330 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_330
  have w14_334 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_334
  have w14_338 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m14]; exact w13_338
  have w14_33c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m14]; exact w13_33c
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_42c
  have b14_424 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m14]; exact b13_424
  have b14_425 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m14]; exact b13_425
  have b14_426 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m14]; exact b13_426
  have b14_427 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m14]; exact b13_427
  clear b13_427 b13_426 b13_425 b13_424 w13_42c w13_428 w13_424 w13_420 w13_33c w13_338 w13_334 w13_330 w13_32c w13_328 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_11 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0xC54: branch, not taken
  obtain ⟨n15, d15, u15⟩ := s14.notTaken E14.self 0xC58 sv_at_c54
    (by decide) (by rw [g14_10, s14.zero]; decide)
  have s15 : St n15.mem SV n15 0xC58 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u15.regs, g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u15.regs, g14_9]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 0x1 := by rw [u15.regs, g14_10]
  have g15_11 : reg n15 a1 = BitVec.ofNat 32 0x1 := by rw [u15.regs, g14_11]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_328 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_328
  have w15_32c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_32c
  have w15_330 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_330
  have w15_334 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_334
  have w15_338 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m15]; exact w14_338
  have w15_33c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m15]; exact w14_33c
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_42c
  have b15_424 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m15]; exact b14_424
  have b15_425 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m15]; exact b14_425
  have b15_426 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m15]; exact b14_426
  have b15_427 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m15]; exact b14_427
  clear b14_427 b14_426 b14_425 b14_424 w14_42c w14_428 w14_424 w14_420 w14_33c w14_338 w14_334 w14_330 w14_32c w14_328 g14_10 g14_8 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_11 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0xC58: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_c58 (off' := 0xC5C) (by decide)
    (by rw [g15_2, show B + 0x21A0 + 0x33C = B + 0x21A0 + BitVec.ofNat 32 0x33C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s16 : St n16.mem SV n16 0xC5C (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
  have g16_11 : reg n16 a1 = BitVec.ofNat 32 0x1 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_11]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = x27 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
  have g16_10 : reg n16 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_2, show B + 0x21A0 + 0x33C = B + 0x21A0 + BitVec.ofNat 32 0x33C by sv_addr, w15_33c]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_328 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_328
  have w16_32c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_32c
  have w16_330 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m16]; exact w15_330
  have w16_334 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m16]; exact w15_334
  have w16_338 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m16]; exact w15_338
  have w16_33c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m16]; exact w15_33c
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m16]; exact w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m16]; exact w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m16]; exact w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m16]; exact w15_42c
  have b16_424 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m16]; exact b15_424
  have b16_425 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m16]; exact b15_425
  have b16_426 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m16]; exact b15_426
  have b16_427 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m16]; exact b15_427
  clear b15_427 b15_426 b15_425 b15_424 w15_42c w15_428 w15_424 w15_420 w15_33c w15_338 w15_334 w15_330 w15_32c w15_328 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_11 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  by_cases hdrem : (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) = 0
  rotate_left
  · -- 0xC5C: branch, taken
    obtain ⟨n17, d17, u17⟩ := s16.taken E16.self 0x7A4 sv_at_c5c
      (by decide) (by rw [g16_10, s16.zero]; exact br_bne_t hdrem)
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
    have g17_9 : reg n17 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u17.regs, g16_9]
    have g17_10 : reg n17 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [u17.regs, g16_10]
    have g17_11 : reg n17 a1 = BitVec.ofNat 32 0x1 := by rw [u17.regs, g16_11]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = x24 := by rw [u17.regs, g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [u17.regs, g16_27]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_328 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m17]; exact w16_328
    have w17_32c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m17]; exact w16_32c
    have w17_330 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m17]; exact w16_330
    have w17_334 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m17]; exact w16_334
    have w17_338 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m17]; exact w16_338
    have w17_33c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m17]; exact w16_33c
    have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m17]; exact w16_420
    have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m17]; exact w16_424
    have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m17]; exact w16_428
    have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m17]; exact w16_42c
    have b17_424 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m17]; exact b16_424
    have b17_425 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m17]; exact b16_425
    have b17_426 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m17]; exact b16_426
    have b17_427 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m17]; exact b16_427
    clear b16_427 b16_426 b16_425 b16_424 w16_42c w16_428 w16_424 w16_420 w16_33c w16_338 w16_334 w16_330 w16_32c w16_328 g16_10 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_11 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    exact .inl ⟨(fun ⟨tl2', h0', h1', te11', h2', h3', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr11] at h1'; cases h1'; rw [hte11] at h2'; cases h2'; exact hdrem h3'), sv_fail F E17 s17 t17 (fun x hx => (fR17 x hx).trans (fM x hx).symm) V17 hret g17_2 g17_18 hO g17_3 g17_4⟩
  -- 0xC5C: branch, not taken
  obtain ⟨n17, d17, u17⟩ := s16.notTaken E16.self 0xC60 sv_at_c5c
    (by decide) (by rw [g16_10, s16.zero]; exact br_bne_f hdrem)
  have s17 : St n17.mem SV n17 0xC60 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
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
  have g17_9 : reg n17 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u17.regs, g16_9]
  have g17_10 : reg n17 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [u17.regs, g16_10]
  have g17_11 : reg n17 a1 = BitVec.ofNat 32 0x1 := by rw [u17.regs, g16_11]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by rw [u17.regs, g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [u17.regs, g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_328 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m17]; exact w16_328
  have w17_32c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m17]; exact w16_32c
  have w17_330 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m17]; exact w16_330
  have w17_334 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m17]; exact w16_334
  have w17_338 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m17]; exact w16_338
  have w17_33c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m17]; exact w16_33c
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m17]; exact w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m17]; exact w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m17]; exact w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m17]; exact w16_42c
  have b17_424 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m17]; exact b16_424
  have b17_425 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m17]; exact b16_425
  have b17_426 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m17]; exact b16_426
  have b17_427 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m17]; exact b16_427
  clear b16_427 b16_426 b16_425 b16_424 w16_42c w16_428 w16_424 w16_420 w16_33c w16_338 w16_334 w16_330 w16_32c w16_328 g16_10 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_11 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0xC60
  obtain ⟨n18, c18, u18⟩ := s17.block svTr3c60 E17.self svTr3c60_end
    ⟨trivial, trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem SV n18 0xC66 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock svTr3c60 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans c18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by
    rw [rb18, runBlock_reg _ _ _ sp s17.zero (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (3 : Fin 32) s17.zero (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (4 : Fin 32) s17.zero (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb18, runBlock_reg _ _ _ (8 : Fin 32) s17.zero (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by
    rw [rb18, runBlock_reg _ _ _ (9 : Fin 32) s17.zero (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by
    rw [rb18, runBlock_reg _ _ _ (18 : Fin 32) s17.zero (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by
    rw [rb18, runBlock_reg _ _ _ (19 : Fin 32) s17.zero (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by
    rw [rb18, runBlock_reg _ _ _ (20 : Fin 32) s17.zero (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by
    rw [rb18, runBlock_reg _ _ _ (21 : Fin 32) s17.zero (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by
    rw [rb18, runBlock_reg _ _ _ (22 : Fin 32) s17.zero (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by
    rw [rb18, runBlock_reg _ _ _ (23 : Fin 32) s17.zero (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by
    rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by
    rw [rb18, runBlock_reg _ _ _ (25 : Fin 32) s17.zero (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by
    rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by
    rw [rb18, runBlock_reg _ _ _ (27 : Fin 32) s17.zero (by decide), g17_27]
  have g18_10 : reg n18 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svTr3c60, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_10, g17_11, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_11 : reg n18 a1 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svTr3c60, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_10, g17_11, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_328 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m18]; exact w17_328
  have w18_32c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m18]; exact w17_32c
  have w18_330 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m18]; exact w17_330
  have w18_334 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m18]; exact w17_334
  have w18_338 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m18]; exact w17_338
  have w18_33c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m18]; exact w17_33c
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m18]; exact w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m18]; exact w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m18]; exact w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m18]; exact w17_42c
  have b18_424 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m18]; exact b17_424
  have b18_425 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m18]; exact b17_425
  have b18_426 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m18]; exact b17_426
  have b18_427 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m18]; exact b17_427
  clear b17_427 b17_426 b17_425 b17_424 w17_42c w17_428 w17_424 w17_420 w17_33c w17_338 w17_334 w17_330 w17_32c w17_328 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_11 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0xC66: sv_seqF
  obtain ⟨n19, c19, s19, sp19, rk19, K19, Ok19, Er19, fr19⟩ := sv_seqF (oc := 0x420) (dc := 0x320)
    F E18 s18 sv_at_c66 sv_at_c6a (by decide) (by decide) g18_2 g18_10 g18_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w18_328 w18_32c (sd_in.restW hr2)
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keepL K19 (by decide)
  rw [sv_mb fR18 (sd_in.restW hr2)] at Ok19 Er19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [rk19 sp (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk19 (3 : Fin 32) (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk19 (4 : Fin 32) (by decide) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rk19 (8 : Fin 32) (by decide) (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [rk19 (9 : Fin 32) (by decide) (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rk19 (18 : Fin 32) (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rk19 (19 : Fin 32) (by decide) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [rk19 (20 : Fin 32) (by decide) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [rk19 (21 : Fin 32) (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [rk19 (22 : Fin 32) (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [rk19 (23 : Fin 32) (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [rk19 (24 : Fin 32) (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [rk19 (25 : Fin 32) (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [rk19 (26 : Fin 32) (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [rk19 (27 : Fin 32) (by decide) (by decide), g18_27]
  obtain ⟨r19, hr19⟩ : ∃ r, derElement 0x30 (memBytes M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = r := ⟨_, rfl⟩
  rcases r19 with er19 | tl19
  · obtain ⟨z19, -⟩ := Er19 er19 hr19
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8)] := keep_kk18.trans K19
    clear keep_kk18
    have w19_330 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K19.w32 (by decide) (by decide)).trans w18_330
    have w19_334 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := (K19.w32 (by decide) (by decide)).trans w18_334
    have w19_338 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := (K19.w32 (by decide) (by decide)).trans w18_338
    have w19_33c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := (K19.w32 (by decide) (by decide)).trans w18_33c
    have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z19
    clear b18_427 b18_426 b18_425 b18_424 w18_42c w18_428 w18_424 w18_420 w18_33c w18_338 w18_334 w18_330 w18_32c w18_328 g18_11 g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
    -- 0xC6E: lw
    obtain ⟨n20, d20, u20⟩ := s19.lw E19.self sv_at_c6e (off' := 0xC72) (by decide)
      (by rw [g19_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s20 : St n20.mem SV n20 0xC72 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
    have t20 : Steps n0 n20 := t19.trans (.single d20)
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.same m20
    have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_4]
    have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_8]
    have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, upd_ne (by decide) (by decide), g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_19]
    have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_20]
    have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = x24 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_27]
    have g20_9 : reg n20 (9 : Fin 32) = 0 := by
      rw [u20.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g19_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w19_420]
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_330 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m20]; exact w19_330
    have w20_334 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m20]; exact w19_334
    have w20_338 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m20]; exact w19_338
    have w20_33c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m20]; exact w19_33c
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m20]; exact w19_420
    clear w19_420 w19_33c w19_338 w19_334 w19_330 z19
    -- 0xC72: lbu
    obtain ⟨n21, d21, u21⟩ := s20.lbu E20.self sv_at_c72 (off' := 0xC76) (by decide)
    have s21 : St n21.mem SV n21 0xC76 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
    have g21_9 : reg n21 (9 : Fin 32) = 0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_330 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m21]; exact w20_330
    have w21_334 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m21]; exact w20_334
    have w21_338 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m21]; exact w20_338
    have w21_33c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m21]; exact w20_33c
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m21]; exact w20_420
    clear w20_420 w20_33c w20_338 w20_334 w20_330 g20_9 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
    -- 0xC76: branch, taken
    obtain ⟨n22, d22, u22⟩ := s21.taken E21.self 0x7A4 sv_at_c76
      (by decide) (by rw [g21_9, s21.zero]; rfl)
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
    have g22_9 : reg n22 (9 : Fin 32) = 0 := by rw [u22.regs, g21_9]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = x24 := by rw [u22.regs, g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_330 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m22]; exact w21_330
    have w22_334 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m22]; exact w21_334
    have w22_338 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m22]; exact w21_338
    have w22_33c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m22]; exact w21_33c
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m22]; exact w21_420
    clear w21_420 w21_33c w21_338 w21_334 w21_330 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
    exact .inl ⟨(fun ⟨tl2', h0', h1', te11', h2', h3', tl19', h4', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr11] at h1'; cases h1'; rw [hte11] at h2'; cases h2'; rw [hr19] at h4'; cases h4'), sv_fail F E22 s22 t22 (fun x hx => (fR22 x hx).trans (fM x hx).symm) V22 hret g22_2 g22_18 hO g22_3 g22_4⟩
  obtain ⟨o0_19, o4_19, o8_19, o12_19, d8_19, d12_19⟩ := Ok19 tl19 hr19
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8)] := keep_kk18.trans K19
  clear keep_kk18
  have w19_330 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K19.w32 (by decide) (by decide)).trans w18_330
  have w19_334 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := (K19.w32 (by decide) (by decide)).trans w18_334
  have w19_338 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := (K19.w32 (by decide) (by decide)).trans w18_338
  have w19_33c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := (K19.w32 (by decide) (by decide)).trans w18_33c
  have w19_328 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := d8_19
  have w19_32c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := d12_19
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := o0_19
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl19.len := o4_19
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := o8_19
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := o12_19
  clear b18_427 b18_426 b18_425 b18_424 w18_42c w18_428 w18_424 w18_420 w18_33c w18_338 w18_334 w18_330 w18_32c w18_328 g18_11 g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  -- 0xC6E: lw
  obtain ⟨n20, d20, u20⟩ := s19.lw E19.self sv_at_c6e (off' := 0xC72) (by decide)
    (by rw [g19_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s20 : St n20.mem SV n20 0xC72 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_8]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, upd_ne (by decide) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = x24 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_27]
  have g20_9 : reg n20 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by
    rw [u20.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g19_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w19_420]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_328 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m20]; exact w19_328
  have w20_32c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m20]; exact w19_32c
  have w20_330 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m20]; exact w19_330
  have w20_334 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m20]; exact w19_334
  have w20_338 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m20]; exact w19_338
  have w20_33c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m20]; exact w19_33c
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m20]; exact w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl19.len := by rw [m20]; exact w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m20]; exact w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m20]; exact w19_42c
  clear w19_42c w19_428 w19_424 w19_420 w19_32c w19_328 w19_33c w19_338 w19_334 w19_330 d12_19 d8_19 o12_19 o8_19 o4_19 o0_19 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 Er19 Ok19 K19 rk19 sp19 s19 c19
  -- 0xC72: lbu
  obtain ⟨n21, d21, u21⟩ := s20.lbu E20.self sv_at_c72 (off' := 0xC76) (by decide)
  have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl19.len).extractLsb' 0 8 := by
    have h := byte_of_ld w20_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s21 : St n21.mem SV n21 0xC76 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
  have g21_9 : reg n21 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
  have g21_8 : reg n21 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g20_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b20_424]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_328 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m21]; exact w20_328
  have w21_32c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m21]; exact w20_32c
  have w21_330 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m21]; exact w20_330
  have w21_334 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m21]; exact w20_334
  have w21_338 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m21]; exact w20_338
  have w21_33c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m21]; exact w20_33c
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m21]; exact w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl19.len := by rw [m21]; exact w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m21]; exact w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m21]; exact w20_42c
  have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl19.len).extractLsb' 0 8 := by rw [m21]; exact b20_424
  clear w20_42c w20_428 w20_424 w20_420 w20_33c w20_338 w20_334 w20_330 w20_32c w20_328 g20_9 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
  -- 0xC76: branch, not taken
  obtain ⟨n22, d22, u22⟩ := s21.notTaken E21.self 0xC7A sv_at_c76
    (by decide) (by rw [g21_9, s21.zero]; exact br_beq_f ((sd_in.restW hr2).ok_ne hr19))
  have s22 : St n22.mem SV n22 0xC7A (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [u22.regs, g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u22.regs, g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = x24 := by rw [u22.regs, g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_328 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m22]; exact w21_328
  have w22_32c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m22]; exact w21_32c
  have w22_330 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m22]; exact w21_330
  have w22_334 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m22]; exact w21_334
  have w22_338 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m22]; exact w21_338
  have w22_33c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m22]; exact w21_33c
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl19.len := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m22]; exact w21_42c
  have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl19.len).extractLsb' 0 8 := by rw [m22]; exact b21_424
  clear b21_424 w21_42c w21_428 w21_424 w21_420 w21_33c w21_338 w21_334 w21_330 w21_32c w21_328 g21_8 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 b20_424 u21 d21
  -- 0xC7A
  obtain ⟨n23, c23, u23⟩ := s22.block svTr3c7a E22.self svTr3c7a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0xC84 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svTr3c7a (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_8 : reg n23 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by
    rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = out := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by
    rw [rb23, runBlock_reg _ _ _ (20 : Fin 32) s22.zero (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by
    rw [rb23, runBlock_reg _ _ _ (22 : Fin 32) s22.zero (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = x24 := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_10 : reg n23 a0 = B + 0x21A0 + BitVec.ofNat 32 0x345 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svTr3c7a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_11 : reg n23 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svTr3c7a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_12 : reg n23 a2 = BitVec.ofNat 32 0xB := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svTr3c7a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m23]; exact w22_328
  have w23_32c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m23]; exact w22_32c
  have w23_330 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m23]; exact w22_330
  have w23_334 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m23]; exact w22_334
  have w23_338 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m23]; exact w22_338
  have w23_33c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m23]; exact w22_33c
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl19.len := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m23]; exact w22_42c
  have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl19.len).extractLsb' 0 8 := by rw [m23]; exact b22_424
  clear b22_424 w22_42c w22_428 w22_424 w22_420 w22_33c w22_338 w22_334 w22_330 w22_32c w22_328 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  have b23_425 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl19.len).extractLsb' 8 8 := by
    have h := byte_of_ld w23_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b23_426 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl19.len).extractLsb' 16 8 := by
    have h := byte_of_ld w23_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b23_427 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl19.len).extractLsb' 24 8 := by
    have h := byte_of_ld w23_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0xC84: memcpy
  obtain ⟨n24, P24, K24, X24⟩ := sv_mc (c := 0x345) (d := 0x425) (N := 0xB) F E23 s23 sv_at_c84 sv_at_c88
    (by decide) (by decide) g23_2 g23_10 g23_11 g23_12
    (by decide) (by decide) (by decide)
  have s24 := P24.st
  have fr24 := P24.fr
  have t24 : Steps n0 n24 := t23.trans P24.steps
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.keep K24 (by decide)
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [P24.regs sp (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P24.regs (3 : Fin 32) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P24.regs (4 : Fin 32) (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [P24.regs (8 : Fin 32) (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [P24.regs (9 : Fin 32) (by decide), g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [P24.regs (18 : Fin 32) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [P24.regs (19 : Fin 32) (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [P24.regs (20 : Fin 32) (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [P24.regs (21 : Fin 32) (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [P24.regs (22 : Fin 32) (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [P24.regs (23 : Fin 32) (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = x24 := by rw [P24.regs (24 : Fin 32) (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [P24.regs (25 : Fin 32) (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [P24.regs (26 : Fin 32) (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [P24.regs (27 : Fin 32) (by decide), g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB)] := keep_kk23.trans K24.toL
  clear keep_kk23
  have w24_328 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := (K24.w32 (by decide) (by decide)).trans w23_328
  have w24_32c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := (K24.w32 (by decide) (by decide)).trans w23_32c
  have w24_330 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K24.w32 (by decide) (by decide)).trans w23_330
  have w24_334 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := (K24.w32 (by decide) (by decide)).trans w23_334
  have w24_338 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := (K24.w32 (by decide) (by decide)).trans w23_338
  have w24_33c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := (K24.w32 (by decide) (by decide)).trans w23_33c
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K24.w32 (by decide) (by decide)).trans w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl19.len := (K24.w32 (by decide) (by decide)).trans w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K24.w32 (by decide) (by decide)).trans w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := (K24.w32 (by decide) (by decide)).trans w23_42c
  have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl19.len).extractLsb' 0 8 := (K24.b8 (by decide) (by decide)).trans b23_424
  have b24_425 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl19.len).extractLsb' 8 8 := (K24.b8 (by decide) (by decide)).trans b23_425
  have b24_426 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl19.len).extractLsb' 16 8 := (K24.b8 (by decide) (by decide)).trans b23_426
  have b24_427 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl19.len).extractLsb' 24 8 := (K24.b8 (by decide) (by decide)).trans b23_427
  have w24_348 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by
    rw [← w23_428]
    exact ld_cp fun q hq => by
      have := X24 (0x3 + q) (by omega)
      rwa [show 0x345 + (0x3 + q) = 0x348 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w24_34c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = BitVec.ofNat 32 tl19.len := by
    rw [← w23_42c]
    exact ld_cp fun q hq => by
      have := X24 (0x7 + q) (by omega)
      rwa [show 0x345 + (0x7 + q) = 0x34C + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b24_345 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x345) = (BitVec.ofNat 32 tl19.len).extractLsb' 8 8 := by rw [show 0x345 = 0x345 + 0x0 from rfl, X24 0x0 (by decide)]; exact b23_425
  have b24_346 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x346) = (BitVec.ofNat 32 tl19.len).extractLsb' 16 8 := by rw [show 0x346 = 0x345 + 0x1 from rfl, X24 0x1 (by decide)]; exact b23_426
  have b24_347 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x347) = (BitVec.ofNat 32 tl19.len).extractLsb' 24 8 := by rw [show 0x347 = 0x345 + 0x2 from rfl, X24 0x2 (by decide)]; exact b23_427
  clear b23_424 w23_42c w23_428 w23_424 w23_420 w23_33c w23_338 w23_334 w23_330 w23_32c w23_328 g23_12 g23_11 g23_10 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0xC8C: sw
  obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_c8c (off' := 0xC90) (c := 0x340)
    (by decide) (by rw [g24_2]; sv_addr) (by decide) (by decide)
  have t25 : Steps n0 n25 := t24.trans d25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg25 (8 : Fin 32), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [rg25 (9 : Fin 32), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [rg25 (20 : Fin 32), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rg25 (21 : Fin 32), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [rg25 (22 : Fin 32), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [rg25 (23 : Fin 32), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = x24 := by rw [rg25 (24 : Fin 32), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rg25 (25 : Fin 32), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rg25 (26 : Fin 32), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = x27 := by rw [rg25 (27 : Fin 32), g24_27]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4)] := keep_kk24.trans K25.toL
  clear keep_kk24
  have w25_328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := (K25.w32 (by decide) (by decide)).trans w24_328
  have w25_32c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := (K25.w32 (by decide) (by decide)).trans w24_32c
  have w25_330 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K25.w32 (by decide) (by decide)).trans w24_330
  have w25_334 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := (K25.w32 (by decide) (by decide)).trans w24_334
  have w25_338 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := (K25.w32 (by decide) (by decide)).trans w24_338
  have w25_33c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := (K25.w32 (by decide) (by decide)).trans w24_33c
  have w25_348 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K25.w32 (by decide) (by decide)).trans w24_348
  have w25_34c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = BitVec.ofNat 32 tl19.len := (K25.w32 (by decide) (by decide)).trans w24_34c
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K25.w32 (by decide) (by decide)).trans w24_420
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl19.len := (K25.w32 (by decide) (by decide)).trans w24_424
  have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K25.w32 (by decide) (by decide)).trans w24_428
  have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := (K25.w32 (by decide) (by decide)).trans w24_42c
  have b25_345 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x345) = (BitVec.ofNat 32 tl19.len).extractLsb' 8 8 := (K25.b8 (by decide) (by decide)).trans b24_345
  have b25_346 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x346) = (BitVec.ofNat 32 tl19.len).extractLsb' 16 8 := (K25.b8 (by decide) (by decide)).trans b24_346
  have b25_347 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x347) = (BitVec.ofNat 32 tl19.len).extractLsb' 24 8 := (K25.b8 (by decide) (by decide)).trans b24_347
  have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl19.len).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_424
  have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl19.len).extractLsb' 8 8 := (K25.b8 (by decide) (by decide)).trans b24_425
  have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl19.len).extractLsb' 16 8 := (K25.b8 (by decide) (by decide)).trans b24_426
  have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl19.len).extractLsb' 24 8 := (K25.b8 (by decide) (by decide)).trans b24_427
  have w25_340 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [W25, g24_9]
  clear b24_347 b24_346 b24_345 w24_34c w24_348 b24_427 b24_426 b24_425 b24_424 w24_42c w24_428 w24_424 w24_420 w24_33c w24_338 w24_334 w24_330 w24_32c w24_328 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 s24 X24 K24 P24 b23_427 b23_426 b23_425
  -- 0xC90: sb
  obtain ⟨n26, d26, s26, fr26, K26, W26, rg26⟩ := sv_sb F E25 s25 sv_at_c90 (off' := 0xC94) (c := 0x344)
    (by decide) (by rw [g25_2]; sv_addr) (by decide)
  have t26 : Steps n0 n26 := t25.trans d26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [rg26 sp, g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg26 (3 : Fin 32), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg26 (4 : Fin 32), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg26 (8 : Fin 32), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [rg26 (9 : Fin 32), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [rg26 (18 : Fin 32), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [rg26 (19 : Fin 32), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [rg26 (20 : Fin 32), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [rg26 (21 : Fin 32), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [rg26 (22 : Fin 32), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [rg26 (23 : Fin 32), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [rg26 (24 : Fin 32), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [rg26 (25 : Fin 32), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [rg26 (26 : Fin 32), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [rg26 (27 : Fin 32), g25_27]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1)] := keep_kk25.trans K26.toL
  clear keep_kk25
  have w26_328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := (K26.w32 (by decide) (by decide)).trans w25_328
  have w26_32c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := (K26.w32 (by decide) (by decide)).trans w25_32c
  have w26_330 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K26.w32 (by decide) (by decide)).trans w25_330
  have w26_334 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := (K26.w32 (by decide) (by decide)).trans w25_334
  have w26_338 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := (K26.w32 (by decide) (by decide)).trans w25_338
  have w26_33c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := (K26.w32 (by decide) (by decide)).trans w25_33c
  have w26_340 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K26.w32 (by decide) (by decide)).trans w25_340
  have w26_348 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K26.w32 (by decide) (by decide)).trans w25_348
  have w26_34c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = BitVec.ofNat 32 tl19.len := (K26.w32 (by decide) (by decide)).trans w25_34c
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K26.w32 (by decide) (by decide)).trans w25_420
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl19.len := (K26.w32 (by decide) (by decide)).trans w25_424
  have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K26.w32 (by decide) (by decide)).trans w25_428
  have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := (K26.w32 (by decide) (by decide)).trans w25_42c
  have b26_345 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x345) = (BitVec.ofNat 32 tl19.len).extractLsb' 8 8 := (K26.b8 (by decide) (by decide)).trans b25_345
  have b26_346 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x346) = (BitVec.ofNat 32 tl19.len).extractLsb' 16 8 := (K26.b8 (by decide) (by decide)).trans b25_346
  have b26_347 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x347) = (BitVec.ofNat 32 tl19.len).extractLsb' 24 8 := (K26.b8 (by decide) (by decide)).trans b25_347
  have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl19.len).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_424
  have b26_425 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl19.len).extractLsb' 8 8 := (K26.b8 (by decide) (by decide)).trans b25_425
  have b26_426 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl19.len).extractLsb' 16 8 := (K26.b8 (by decide) (by decide)).trans b25_426
  have b26_427 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl19.len).extractLsb' 24 8 := (K26.b8 (by decide) (by decide)).trans b25_427
  have b26_344 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = (BitVec.ofNat 32 tl19.len).extractLsb' 0 8 := by rw [W26, g25_8, lbu_low]
  clear w25_340 b25_427 b25_426 b25_425 b25_424 b25_347 b25_346 b25_345 w25_42c w25_428 w25_424 w25_420 w25_34c w25_348 w25_33c w25_338 w25_334 w25_330 w25_32c w25_328 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
  have w26_344 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := ld_of_bytes b26_344
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x344 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x345 by sv_addr]; exact b26_345)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x344 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x346 by sv_addr]; exact b26_346)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x344 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x347 by sv_addr]; exact b26_347)
  -- 0xC94
  obtain ⟨n27, c27, u27⟩ := s26.block svTr3c94 E26.self svTr3c94_end
    ⟨trivial, trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem SV n27 0xC9A (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock svTr3c94 (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
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
  have g27_8 : reg n27 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by
    rw [rb27, runBlock_reg _ _ _ (9 : Fin 32) s26.zero (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by
    rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by
    rw [rb27, runBlock_reg _ _ _ (20 : Fin 32) s26.zero (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by
    rw [rb27, runBlock_reg _ _ _ (21 : Fin 32) s26.zero (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by
    rw [rb27, runBlock_reg _ _ _ (22 : Fin 32) s26.zero (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by
    rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = x24 := by
    rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by
    rw [rb27, runBlock_reg _ _ _ (25 : Fin 32) s26.zero (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = x27 := by
    rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
  have g27_10 : reg n27 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svTr3c94, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g27_11 : reg n27 a1 = B + 0x21A0 + BitVec.ofNat 32 0x340 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svTr3c94, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m27]; exact w26_328
  have w27_32c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m27]; exact w26_32c
  have w27_330 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m27]; exact w26_330
  have w27_334 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m27]; exact w26_334
  have w27_338 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m27]; exact w26_338
  have w27_33c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m27]; exact w26_33c
  have w27_340 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m27]; exact w26_340
  have w27_344 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m27]; exact w26_344
  have w27_348 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m27]; exact w26_348
  have w27_34c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = BitVec.ofNat 32 tl19.len := by rw [m27]; exact w26_34c
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m27]; exact w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl19.len := by rw [m27]; exact w26_424
  have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m27]; exact w26_428
  have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m27]; exact w26_42c
  have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl19.len).extractLsb' 0 8 := by rw [m27]; exact b26_424
  have b27_425 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl19.len).extractLsb' 8 8 := by rw [m27]; exact b26_425
  have b27_426 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl19.len).extractLsb' 16 8 := by rw [m27]; exact b26_426
  have b27_427 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl19.len).extractLsb' 24 8 := by rw [m27]; exact b26_427
  clear b26_344 b26_427 b26_426 b26_425 b26_424 b26_347 b26_346 b26_345 w26_42c w26_428 w26_424 w26_420 w26_34c w26_348 w26_340 w26_33c w26_338 w26_334 w26_330 w26_32c w26_328 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 rg26 W26 K26 fr26 s26 d26
  -- 0xC9A: sv_oidF
  obtain ⟨n28, c28, s28, sp28, rk28, K28, A28, Ok28, Er28, fr28⟩ := sv_oidF (oc := 0x420) (dc := 0x340)
    F E27 s27 sv_at_c9a sv_at_c9e (by decide) (by decide) g27_2 g27_10 g27_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w27_348 w27_34c ((sd_in.restW hr2).contentW hr19)
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keepL K28 (by decide)
  rw [sv_mb fR27 ((sd_in.restW hr2).contentW hr19)] at A28 Ok28 Er28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rk28 sp (by decide) (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk28 (3 : Fin 32) (by decide) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk28 (4 : Fin 32) (by decide) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk28 (8 : Fin 32) (by decide) (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [rk28 (9 : Fin 32) (by decide) (by decide), g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rk28 (18 : Fin 32) (by decide) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rk28 (19 : Fin 32) (by decide) (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [rk28 (20 : Fin 32) (by decide) (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [rk28 (21 : Fin 32) (by decide) (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [rk28 (22 : Fin 32) (by decide) (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [rk28 (23 : Fin 32) (by decide) (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [rk28 (24 : Fin 32) (by decide) (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [rk28 (25 : Fin 32) (by decide) (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [rk28 (26 : Fin 32) (by decide) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [rk28 (27 : Fin 32) (by decide) (by decide), g27_27]
  obtain ⟨r28, hr28⟩ : ∃ r, derContent (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) (derOid (memBytes M0 (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) (BitVec.ofNat 32 tl19.len).toNat)) = r := ⟨_, rfl⟩
  rcases r28 with er28 | ⟨op28, ol28⟩
  · obtain ⟨z28, -⟩ := Er28 er28 hr28
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := keep_kk27.trans K28
    clear keep_kk27
    have w28_328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := (K28.w32 (by decide) (by decide)).trans w27_328
    have w28_32c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := (K28.w32 (by decide) (by decide)).trans w27_32c
    have w28_330 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K28.w32 (by decide) (by decide)).trans w27_330
    have w28_334 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := (K28.w32 (by decide) (by decide)).trans w27_334
    have w28_338 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := (K28.w32 (by decide) (by decide)).trans w27_338
    have w28_33c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := (K28.w32 (by decide) (by decide)).trans w27_33c
    have w28_340 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K28.w32 (by decide) (by decide)).trans w27_340
    have w28_344 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := (K28.w32 (by decide) (by decide)).trans w27_344
    have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K28.w32 (by decide) (by decide)).trans w27_428
    have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := (K28.w32 (by decide) (by decide)).trans w27_42c
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z28
    clear b27_427 b27_426 b27_425 b27_424 w27_42c w27_428 w27_424 w27_420 w27_34c w27_348 w27_344 w27_340 w27_33c w27_338 w27_334 w27_330 w27_32c w27_328 g27_11 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27 w26_344
    -- 0xCA2: lw
    obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_ca2 (off' := 0xCA6) (by decide)
      (by rw [g28_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s29 : St n29.mem SV n29 0xCA6 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = x27 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
    have g29_10 : reg n29 a0 = 0 := by
      rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g28_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w28_420]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_328 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m29]; exact w28_328
    have w29_32c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m29]; exact w28_32c
    have w29_330 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m29]; exact w28_330
    have w29_334 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m29]; exact w28_334
    have w29_338 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m29]; exact w28_338
    have w29_33c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m29]; exact w28_33c
    have w29_340 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m29]; exact w28_340
    have w29_344 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m29]; exact w28_344
    have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m29]; exact w28_420
    have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m29]; exact w28_428
    have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m29]; exact w28_42c
    clear w28_420 w28_42c w28_428 w28_344 w28_340 w28_33c w28_338 w28_334 w28_330 w28_32c w28_328 z28
    -- 0xCA6: branch, taken
    obtain ⟨n30, d30, u30⟩ := s29.taken E29.self 0x12AA sv_at_ca6
      (by decide) (by rw [g29_10, s29.zero]; rfl)
    have s30 : St n30.mem SV n30 0x12AA (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [u30.regs, g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u30.regs, g29_9]
    have g30_10 : reg n30 a0 = 0 := by rw [u30.regs, g29_10]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [u30.regs, g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [u30.regs, g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [u30.regs, g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [u30.regs, g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = x24 := by rw [u30.regs, g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [u30.regs, g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [u30.regs, g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = x27 := by rw [u30.regs, g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_328 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m30]; exact w29_328
    have w30_32c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m30]; exact w29_32c
    have w30_330 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m30]; exact w29_330
    have w30_334 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m30]; exact w29_334
    have w30_338 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m30]; exact w29_338
    have w30_33c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m30]; exact w29_33c
    have w30_340 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m30]; exact w29_340
    have w30_344 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m30]; exact w29_344
    have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m30]; exact w29_420
    have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m30]; exact w29_428
    have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m30]; exact w29_42c
    clear w29_42c w29_428 w29_420 w29_344 w29_340 w29_33c w29_338 w29_334 w29_330 w29_32c w29_328 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
    -- 0x12AA: lbu
    obtain ⟨n31, d31, u31⟩ := s30.lbu E30.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s31 : St n31.mem SV n31 0x12AE (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
    have g31_9 : reg n31 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
    have g31_10 : reg n31 a0 = 0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_10]
    have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = x24 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = x25 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = x27 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_328 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m31]; exact w30_328
    have w31_32c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m31]; exact w30_32c
    have w31_330 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m31]; exact w30_330
    have w31_334 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m31]; exact w30_334
    have w31_338 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m31]; exact w30_338
    have w31_33c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m31]; exact w30_33c
    have w31_340 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m31]; exact w30_340
    have w31_344 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m31]; exact w30_344
    have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m31]; exact w30_420
    have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m31]; exact w30_428
    have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m31]; exact w30_42c
    clear w30_42c w30_428 w30_420 w30_344 w30_340 w30_33c w30_338 w30_334 w30_330 w30_32c w30_328 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
    -- 0x12AE: j
    obtain ⟨n32, d32, u32⟩ := s31.jump E31.self sv_at_12ae (off' := 0x7A4) (by decide)
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
    have g32_9 : reg n32 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = 0 := by rw [u32.regs, g31_10]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = x24 := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = x25 := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = x27 := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_328 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m32]; exact w31_328
    have w32_32c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m32]; exact w31_32c
    have w32_330 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m32]; exact w31_330
    have w32_334 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m32]; exact w31_334
    have w32_338 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m32]; exact w31_338
    have w32_33c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m32]; exact w31_33c
    have w32_340 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m32]; exact w31_340
    have w32_344 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m32]; exact w31_344
    have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m32]; exact w31_420
    have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m32]; exact w31_428
    have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m32]; exact w31_42c
    clear w31_42c w31_428 w31_420 w31_344 w31_340 w31_33c w31_338 w31_334 w31_330 w31_32c w31_328 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    exact .inl ⟨(fun ⟨tl2', h0', h1', te11', h2', h3', tl19', h4', op28', ol28', h5', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr11] at h1'; cases h1'; rw [hte11] at h2'; cases h2'; rw [hr19] at h4'; cases h4'; rw [hr28] at h5'; cases h5'), sv_fail F E32 s32 t32 (fun x hx => (fR32 x hx).trans (fM x hx).symm) V32 hret g32_2 g32_18 hO g32_3 g32_4⟩
  obtain ⟨to28, ht28, -, -⟩ := oid_ok_content hr28
  obtain ⟨p0_28, p4_28⟩ := Ok28 op28 ol28 hr28
  obtain ⟨d8_28, d12_28⟩ := A28 to28 (derOid_ok_elem ht28)
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := keep_kk27.trans K28
  clear keep_kk27
  have w28_328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := (K28.w32 (by decide) (by decide)).trans w27_328
  have w28_32c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := (K28.w32 (by decide) (by decide)).trans w27_32c
  have w28_330 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K28.w32 (by decide) (by decide)).trans w27_330
  have w28_334 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := (K28.w32 (by decide) (by decide)).trans w27_334
  have w28_338 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := (K28.w32 (by decide) (by decide)).trans w27_338
  have w28_33c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := (K28.w32 (by decide) (by decide)).trans w27_33c
  have w28_340 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K28.w32 (by decide) (by decide)).trans w27_340
  have w28_344 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := (K28.w32 (by decide) (by decide)).trans w27_344
  have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K28.w32 (by decide) (by decide)).trans w27_428
  have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := (K28.w32 (by decide) (by decide)).trans w27_42c
  have w28_348 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) + BitVec.ofNat 32 (to28.header + to28.len) := d8_28
  have w28_34c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (BitVec.ofNat 32 tl19.len) - BitVec.ofNat 32 (to28.header + to28.len) := d12_28
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op28 := p0_28
  have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol28 := p4_28
  clear b27_427 b27_426 b27_425 b27_424 w27_42c w27_428 w27_424 w27_420 w27_34c w27_348 w27_344 w27_340 w27_33c w27_338 w27_334 w27_330 w27_32c w27_328 g27_11 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27 w26_344
  -- 0xCA2: lw
  obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_ca2 (off' := 0xCA6) (by decide)
    (by rw [g28_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s29 : St n29.mem SV n29 0xCA6 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = x27 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
  have g29_10 : reg n29 a0 = op28 := by
    rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g28_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w28_420]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_328 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m29]; exact w28_328
  have w29_32c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m29]; exact w28_32c
  have w29_330 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m29]; exact w28_330
  have w29_334 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m29]; exact w28_334
  have w29_338 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m29]; exact w28_338
  have w29_33c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m29]; exact w28_33c
  have w29_340 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m29]; exact w28_340
  have w29_344 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m29]; exact w28_344
  have w29_348 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) + BitVec.ofNat 32 (to28.header + to28.len) := by rw [m29]; exact w28_348
  have w29_34c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (BitVec.ofNat 32 tl19.len) - BitVec.ofNat 32 (to28.header + to28.len) := by rw [m29]; exact w28_34c
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op28 := by rw [m29]; exact w28_420
  have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol28 := by rw [m29]; exact w28_424
  have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m29]; exact w28_428
  have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m29]; exact w28_42c
  clear w28_424 w28_420 w28_34c w28_348 w28_42c w28_428 w28_344 w28_340 w28_33c w28_338 w28_334 w28_330 w28_32c w28_328 d12_28 d8_28 p4_28 p0_28 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 Er28 Ok28 A28 K28 rk28 sp28 s28 c28
  -- 0xCA6: branch, not taken
  obtain ⟨n30, d30, u30⟩ := s29.notTaken E29.self 0xCAA sv_at_ca6
    (by decide) (by rw [g29_10, s29.zero]; exact br_beq_f ((((sd_in.restW hr2).contentW hr19).oidIn hr28).pos_ne))
  have s30 : St n30.mem SV n30 0xCAA (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [u30.regs, g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u30.regs, g29_9]
  have g30_10 : reg n30 a0 = op28 := by rw [u30.regs, g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [u30.regs, g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [u30.regs, g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [u30.regs, g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [u30.regs, g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = x24 := by rw [u30.regs, g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [u30.regs, g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [u30.regs, g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = x27 := by rw [u30.regs, g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_328 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m30]; exact w29_328
  have w30_32c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m30]; exact w29_32c
  have w30_330 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m30]; exact w29_330
  have w30_334 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m30]; exact w29_334
  have w30_338 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m30]; exact w29_338
  have w30_33c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m30]; exact w29_33c
  have w30_340 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m30]; exact w29_340
  have w30_344 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m30]; exact w29_344
  have w30_348 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) + BitVec.ofNat 32 (to28.header + to28.len) := by rw [m30]; exact w29_348
  have w30_34c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (BitVec.ofNat 32 tl19.len) - BitVec.ofNat 32 (to28.header + to28.len) := by rw [m30]; exact w29_34c
  have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op28 := by rw [m30]; exact w29_420
  have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol28 := by rw [m30]; exact w29_424
  have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m30]; exact w29_428
  have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m30]; exact w29_42c
  clear w29_42c w29_428 w29_424 w29_420 w29_34c w29_348 w29_344 w29_340 w29_33c w29_338 w29_334 w29_330 w29_32c w29_328 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  -- 0xCAA: lw
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_caa (off' := 0xCAE) (by decide)
    (by rw [g30_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s31 : St n31.mem SV n31 0xCAE (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
  have g31_10 : reg n31 a0 = op28 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_10]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = x24 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = x25 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = x27 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
  have g31_11 : reg n31 a1 = ol28 := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w30_424]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_328 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m31]; exact w30_328
  have w31_32c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m31]; exact w30_32c
  have w31_330 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m31]; exact w30_330
  have w31_334 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m31]; exact w30_334
  have w31_338 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m31]; exact w30_338
  have w31_33c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m31]; exact w30_33c
  have w31_340 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m31]; exact w30_340
  have w31_344 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m31]; exact w30_344
  have w31_348 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) + BitVec.ofNat 32 (to28.header + to28.len) := by rw [m31]; exact w30_348
  have w31_34c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (BitVec.ofNat 32 tl19.len) - BitVec.ofNat 32 (to28.header + to28.len) := by rw [m31]; exact w30_34c
  have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op28 := by rw [m31]; exact w30_420
  have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol28 := by rw [m31]; exact w30_424
  have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m31]; exact w30_428
  have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m31]; exact w30_42c
  clear w30_42c w30_428 w30_424 w30_420 w30_34c w30_348 w30_344 w30_340 w30_33c w30_338 w30_334 w30_330 w30_32c w30_328 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
  -- 0xCAE
  obtain ⟨n32, c32, u32⟩ := s31.block svTr3cae E31.self svTr3cae_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have s32 : St n32.mem SV n32 0xCB8 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have rb32 : ∀ q, reg n32 q = (runBlock svTr3cae (n31.mem, reg n31)).2 q := fun q => by rw [u32.regs]
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
  have g32_8 : reg n32 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb32, runBlock_reg _ _ _ (8 : Fin 32) s31.zero (by decide), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by
    rw [rb32, runBlock_reg _ _ _ (9 : Fin 32) s31.zero (by decide), g31_9]
  have g32_10 : reg n32 a0 = op28 := by
    rw [rb32, runBlock_reg _ _ _ a0 s31.zero (by decide), g31_10]
  have g32_11 : reg n32 a1 = ol28 := by
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
  have g32_24 : reg n32 (24 : Fin 32) = x24 := by
    rw [rb32, runBlock_reg _ _ _ (24 : Fin 32) s31.zero (by decide), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = x25 := by
    rw [rb32, runBlock_reg _ _ _ (25 : Fin 32) s31.zero (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by
    rw [rb32, runBlock_reg _ _ _ (26 : Fin 32) s31.zero (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = x27 := by
    rw [rb32, runBlock_reg _ _ _ (27 : Fin 32) s31.zero (by decide), g31_27]
  have g32_12 : reg n32 a2 = BitVec.ofNat 32 (img% svConstCmsAddress + 0x9) := by
    rw [rb32]; simp +decide only [runBlock, BInstr.run, svTr3cae, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g31_2, g31_3, g31_4, g31_8, g31_9, g31_10, g31_11, g31_18, g31_19, g31_20, g31_21, g31_22, g31_23, g31_24, g31_25, g31_26, g31_27, s31.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g32_13 : reg n32 a3 = BitVec.ofNat 32 0xB := by
    rw [rb32]; simp +decide only [runBlock, BInstr.run, svTr3cae, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g31_2, g31_3, g31_4, g31_8, g31_9, g31_10, g31_11, g31_18, g31_19, g31_20, g31_21, g31_22, g31_23, g31_24, g31_25, g31_26, g31_27, s31.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_328 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m32]; exact w31_328
  have w32_32c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m32]; exact w31_32c
  have w32_330 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m32]; exact w31_330
  have w32_334 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m32]; exact w31_334
  have w32_338 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m32]; exact w31_338
  have w32_33c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m32]; exact w31_33c
  have w32_340 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m32]; exact w31_340
  have w32_344 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m32]; exact w31_344
  have w32_348 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) + BitVec.ofNat 32 (to28.header + to28.len) := by rw [m32]; exact w31_348
  have w32_34c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (BitVec.ofNat 32 tl19.len) - BitVec.ofNat 32 (to28.header + to28.len) := by rw [m32]; exact w31_34c
  have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op28 := by rw [m32]; exact w31_420
  have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol28 := by rw [m32]; exact w31_424
  have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m32]; exact w31_428
  have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m32]; exact w31_42c
  clear w31_42c w31_428 w31_424 w31_420 w31_34c w31_348 w31_344 w31_340 w31_33c w31_338 w31_334 w31_330 w31_32c w31_328 g31_11 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0xCB8: sv_sneF
  obtain ⟨n33, c33, s33, rk33, a0_33, K33, fr33⟩ := sv_sneF (pl := ol28.toNat) (ql := 11)
    F E32 s32 sv_at_cb8 sv_at_cbc (by decide) (by decide) g32_2
    g32_10 (by rw [g32_11, ofNat_toNat_self]) g32_12 g32_13 (.inl (((sd_in.restW hr2).contentW hr19).oidIn hr28)) (.inr ⟨by decide, by decide⟩)
  have t33 : Steps n0 n33 := t32.trans c33
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.keepL K33 (by decide)
  rw [sv_mbRo FW fR32 (.inl (((sd_in.restW hr2).contentW hr19).oidIn hr28)), sv_mbRo FW fR32 (.inr ⟨by decide, by decide⟩)] at a0_33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [rk33 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk33 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk33 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk33 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [rk33 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_9]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [rk33 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [rk33 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = x20 := by rw [rk33 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = x21 := by rw [rk33 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = x22 := by rw [rk33 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = x23 := by rw [rk33 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = x24 := by rw [rk33 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = x25 := by rw [rk33 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [rk33 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = x27 := by rw [rk33 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g32_27]
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := keep_kk32.trans K33
  clear keep_kk32
  have w33_328 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := (K33.w32 (by decide) (by decide)).trans w32_328
  have w33_32c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := (K33.w32 (by decide) (by decide)).trans w32_32c
  have w33_330 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := (K33.w32 (by decide) (by decide)).trans w32_330
  have w33_334 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := (K33.w32 (by decide) (by decide)).trans w32_334
  have w33_338 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := (K33.w32 (by decide) (by decide)).trans w32_338
  have w33_33c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := (K33.w32 (by decide) (by decide)).trans w32_33c
  have w33_340 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K33.w32 (by decide) (by decide)).trans w32_340
  have w33_344 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := (K33.w32 (by decide) (by decide)).trans w32_344
  have w33_348 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) + BitVec.ofNat 32 (to28.header + to28.len) := (K33.w32 (by decide) (by decide)).trans w32_348
  have w33_34c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (BitVec.ofNat 32 tl19.len) - BitVec.ofNat 32 (to28.header + to28.len) := (K33.w32 (by decide) (by decide)).trans w32_34c
  have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op28 := (K33.w32 (by decide) (by decide)).trans w32_420
  have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol28 := (K33.w32 (by decide) (by decide)).trans w32_424
  have w33_428 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := (K33.w32 (by decide) (by decide)).trans w32_428
  have w33_42c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := (K33.w32 (by decide) (by decide)).trans w32_42c
  clear w32_42c w32_428 w32_424 w32_420 w32_34c w32_348 w32_344 w32_340 w32_33c w32_338 w32_334 w32_330 w32_32c w32_328 g32_13 g32_12 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 rb32 s32 m32 u32 c32
  by_cases htst : memBytes M0 op28 ol28.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11
  rotate_left
  · have g33_10 : reg n33 a0 = BitVec.ofNat 32 1 := by rw [a0_33, ite_eq_right htst]; rfl
    -- 0xCC0: branch, taken
    obtain ⟨n34, d34, u34⟩ := s33.taken E33.self 0x12B8 sv_at_cc0
      (by decide) (by rw [g33_10, s33.zero]; decide)
    have s34 : St n34.mem SV n34 0x12B8 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
    have m34 : n34.mem = n33.mem := u34.mem
    have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
    have t34 : Steps n0 n34 := t33.trans (.single d34)
    have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.same m34
    have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, g33_4]
    have g34_8 : reg n34 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [u34.regs, g33_8]
    have g34_9 : reg n34 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u34.regs, g33_9]
    have g34_10 : reg n34 a0 = BitVec.ofNat 32 0x1 := by rw [u34.regs, g33_10]
    have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, g33_18]
    have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, g33_19]
    have g34_20 : reg n34 (20 : Fin 32) = x20 := by rw [u34.regs, g33_20]
    have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [u34.regs, g33_21]
    have g34_22 : reg n34 (22 : Fin 32) = x22 := by rw [u34.regs, g33_22]
    have g34_23 : reg n34 (23 : Fin 32) = x23 := by rw [u34.regs, g33_23]
    have g34_24 : reg n34 (24 : Fin 32) = x24 := by rw [u34.regs, g33_24]
    have g34_25 : reg n34 (25 : Fin 32) = x25 := by rw [u34.regs, g33_25]
    have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [u34.regs, g33_26]
    have g34_27 : reg n34 (27 : Fin 32) = x27 := by rw [u34.regs, g33_27]
    have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m34]; exact keep_kk33
    clear keep_kk33
    have w34_328 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m34]; exact w33_328
    have w34_32c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m34]; exact w33_32c
    have w34_330 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m34]; exact w33_330
    have w34_334 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m34]; exact w33_334
    have w34_338 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m34]; exact w33_338
    have w34_33c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m34]; exact w33_33c
    have w34_340 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m34]; exact w33_340
    have w34_344 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m34]; exact w33_344
    have w34_348 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) + BitVec.ofNat 32 (to28.header + to28.len) := by rw [m34]; exact w33_348
    have w34_34c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (BitVec.ofNat 32 tl19.len) - BitVec.ofNat 32 (to28.header + to28.len) := by rw [m34]; exact w33_34c
    have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op28 := by rw [m34]; exact w33_420
    have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol28 := by rw [m34]; exact w33_424
    have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m34]; exact w33_428
    have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m34]; exact w33_42c
    clear w33_42c w33_428 w33_424 w33_420 w33_34c w33_348 w33_344 w33_340 w33_33c w33_338 w33_334 w33_330 w33_32c w33_328 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 K33 a0_33 rk33 s33 c33
    -- 0x12B8
    obtain ⟨n35, c35, u35⟩ := s34.block svTr312b8 E34.self svTr312b8_end
      ⟨trivial, trivial⟩
    have m35 : n35.mem = n34.mem := u35.mem
    have s35 : St n35.mem SV n35 0x12BA (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
    have rb35 : ∀ q, reg n35 q = (runBlock svTr312b8 (n34.mem, reg n34)).2 q := fun q => by rw [u35.regs]
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
    have g35_9 : reg n35 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by
      rw [rb35, runBlock_reg _ _ _ (9 : Fin 32) s34.zero (by decide), g34_9]
    have g35_10 : reg n35 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb35, runBlock_reg _ _ _ a0 s34.zero (by decide), g34_10]
    have g35_18 : reg n35 (18 : Fin 32) = out := by
      rw [rb35, runBlock_reg _ _ _ (18 : Fin 32) s34.zero (by decide), g34_18]
    have g35_19 : reg n35 (19 : Fin 32) = bp := by
      rw [rb35, runBlock_reg _ _ _ (19 : Fin 32) s34.zero (by decide), g34_19]
    have g35_20 : reg n35 (20 : Fin 32) = x20 := by
      rw [rb35, runBlock_reg _ _ _ (20 : Fin 32) s34.zero (by decide), g34_20]
    have g35_21 : reg n35 (21 : Fin 32) = x21 := by
      rw [rb35, runBlock_reg _ _ _ (21 : Fin 32) s34.zero (by decide), g34_21]
    have g35_22 : reg n35 (22 : Fin 32) = x22 := by
      rw [rb35, runBlock_reg _ _ _ (22 : Fin 32) s34.zero (by decide), g34_22]
    have g35_23 : reg n35 (23 : Fin 32) = x23 := by
      rw [rb35, runBlock_reg _ _ _ (23 : Fin 32) s34.zero (by decide), g34_23]
    have g35_24 : reg n35 (24 : Fin 32) = x24 := by
      rw [rb35, runBlock_reg _ _ _ (24 : Fin 32) s34.zero (by decide), g34_24]
    have g35_25 : reg n35 (25 : Fin 32) = x25 := by
      rw [rb35, runBlock_reg _ _ _ (25 : Fin 32) s34.zero (by decide), g34_25]
    have g35_26 : reg n35 (26 : Fin 32) = x26 := by
      rw [rb35, runBlock_reg _ _ _ (26 : Fin 32) s34.zero (by decide), g34_26]
    have g35_27 : reg n35 (27 : Fin 32) = x27 := by
      rw [rb35, runBlock_reg _ _ _ (27 : Fin 32) s34.zero (by decide), g34_27]
    have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb35]; simp +decide only [runBlock, BInstr.run, svTr312b8, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_10, g34_18, g34_19, g34_20, g34_21, g34_22, g34_23, g34_24, g34_25, g34_26, g34_27, s34.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m35]; exact keep_kk34
    clear keep_kk34
    have w35_328 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m35]; exact w34_328
    have w35_32c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m35]; exact w34_32c
    have w35_330 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m35]; exact w34_330
    have w35_334 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m35]; exact w34_334
    have w35_338 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m35]; exact w34_338
    have w35_33c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m35]; exact w34_33c
    have w35_340 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m35]; exact w34_340
    have w35_344 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m35]; exact w34_344
    have w35_348 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) + BitVec.ofNat 32 (to28.header + to28.len) := by rw [m35]; exact w34_348
    have w35_34c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (BitVec.ofNat 32 tl19.len) - BitVec.ofNat 32 (to28.header + to28.len) := by rw [m35]; exact w34_34c
    have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op28 := by rw [m35]; exact w34_420
    have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol28 := by rw [m35]; exact w34_424
    have w35_428 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m35]; exact w34_428
    have w35_42c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m35]; exact w34_42c
    clear w34_42c w34_428 w34_424 w34_420 w34_34c w34_348 w34_344 w34_340 w34_33c w34_338 w34_334 w34_330 w34_32c w34_328 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_10 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34 g33_10
    -- 0x12BA: j
    obtain ⟨n36, d36, u36⟩ := s35.jump E35.self sv_at_12ba (off' := 0x7A4) (by decide)
      (by rw [s35.pc]; decide)
    have s36 : St n36.mem SV n36 0x7A4 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
    have m36 : n36.mem = n35.mem := u36.mem
    have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
    have t36 : Steps n0 n36 := t35.trans (.single d36)
    have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
    have E36 : SvCode n36.mem := E35.fr F fr36
    have V36 : SvSaves B n36.mem v := V35.same m36
    have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, g35_2]
    have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, g35_3]
    have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, g35_4]
    have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u36.regs, g35_8]
    have g36_9 : reg n36 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u36.regs, g35_9]
    have g36_10 : reg n36 a0 = BitVec.ofNat 32 0x1 := by rw [u36.regs, g35_10]
    have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, g35_18]
    have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, g35_19]
    have g36_20 : reg n36 (20 : Fin 32) = x20 := by rw [u36.regs, g35_20]
    have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, g35_21]
    have g36_22 : reg n36 (22 : Fin 32) = x22 := by rw [u36.regs, g35_22]
    have g36_23 : reg n36 (23 : Fin 32) = x23 := by rw [u36.regs, g35_23]
    have g36_24 : reg n36 (24 : Fin 32) = x24 := by rw [u36.regs, g35_24]
    have g36_25 : reg n36 (25 : Fin 32) = x25 := by rw [u36.regs, g35_25]
    have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, g35_26]
    have g36_27 : reg n36 (27 : Fin 32) = x27 := by rw [u36.regs, g35_27]
    have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m36]; exact keep_kk35
    clear keep_kk35
    have w36_328 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m36]; exact w35_328
    have w36_32c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m36]; exact w35_32c
    have w36_330 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m36]; exact w35_330
    have w36_334 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m36]; exact w35_334
    have w36_338 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m36]; exact w35_338
    have w36_33c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m36]; exact w35_33c
    have w36_340 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m36]; exact w35_340
    have w36_344 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m36]; exact w35_344
    have w36_348 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) + BitVec.ofNat 32 (to28.header + to28.len) := by rw [m36]; exact w35_348
    have w36_34c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (BitVec.ofNat 32 tl19.len) - BitVec.ofNat 32 (to28.header + to28.len) := by rw [m36]; exact w35_34c
    have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op28 := by rw [m36]; exact w35_420
    have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol28 := by rw [m36]; exact w35_424
    have w36_428 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m36]; exact w35_428
    have w36_42c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m36]; exact w35_42c
    clear w35_42c w35_428 w35_424 w35_420 w35_34c w35_348 w35_344 w35_340 w35_33c w35_338 w35_334 w35_330 w35_32c w35_328 g35_8 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_10 g35_9 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 rb35 s35 m35 u35 c35
    exact .inl ⟨(fun ⟨tl2', h0', h1', te11', h2', h3', tl19', h4', op28', ol28', h5', to28', h6', h7', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr11] at h1'; cases h1'; rw [hte11] at h2'; cases h2'; rw [hr19] at h4'; cases h4'; rw [hr28] at h5'; cases h5'; rw [ht28] at h6'; cases h6'; exact htst h7'), sv_fail F E36 s36 t36 (fun x hx => (fR36 x hx).trans (fM x hx).symm) V36 hret g36_2 g36_18 hO g36_3 g36_4⟩
  have g33_10 : reg n33 a0 = BitVec.ofNat 32 0 := by rw [a0_33, ite_eq_left htst]; rfl
  -- 0xCC0: branch, not taken
  obtain ⟨n34, d34, u34⟩ := s33.notTaken E33.self 0xCC4 sv_at_cc0
    (by decide) (by rw [g33_10, s33.zero]; decide)
  have s34 : St n34.mem SV n34 0xCC4 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans (.single d34)
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = ((BitVec.ofNat 32 tl19.len).extractLsb' 0 8).zeroExtend 32 := by rw [u34.regs, g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [u34.regs, g33_9]
  have g34_10 : reg n34 a0 = BitVec.ofNat 32 0x0 := by rw [u34.regs, g33_10]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = x20 := by rw [u34.regs, g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [u34.regs, g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = x22 := by rw [u34.regs, g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = x23 := by rw [u34.regs, g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = x24 := by rw [u34.regs, g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = x25 := by rw [u34.regs, g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [u34.regs, g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = x27 := by rw [u34.regs, g33_27]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x420, 0x10), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x420, 0x10), (0x328, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x420, 0x8), (0x348, 0x8)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_328 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m34]; exact w33_328
  have w34_32c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl19.header + tl19.len) := by rw [m34]; exact w33_32c
  have w34_330 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m34]; exact w33_330
  have w34_334 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = BitVec.ofNat 32 tl2.len := by rw [m34]; exact w33_334
  have w34_338 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te11.header + te11.len) := by rw [m34]; exact w33_338
  have w34_33c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te11.header + te11.len) := by rw [m34]; exact w33_33c
  have w34_340 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m34]; exact w33_340
  have w34_344 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x344) = BitVec.ofNat 32 tl19.len := by rw [m34]; exact w33_344
  have w34_348 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header) + BitVec.ofNat 32 (to28.header + to28.len) := by rw [m34]; exact w33_348
  have w34_34c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (BitVec.ofNat 32 tl19.len) - BitVec.ofNat 32 (to28.header + to28.len) := by rw [m34]; exact w33_34c
  have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op28 := by rw [m34]; exact w33_420
  have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol28 := by rw [m34]; exact w33_424
  have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl19.header := by rw [m34]; exact w33_428
  have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl19.len := by rw [m34]; exact w33_42c
  clear w33_42c w33_428 w33_424 w33_420 w33_34c w33_348 w33_344 w33_340 w33_33c w33_338 w33_334 w33_330 w33_32c w33_328 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 K33 a0_33 rk33 s33 c33
  exact .inr ⟨tl2, hr2, hr11, te11, hte11, hdrem, tl19, hr19, op28, ol28, hr28, to28, ht28, htst, n34, t34, s34, E34, V34, fR34, g34_2, g34_3, g34_4, g34_18, g34_19, g34_20, g34_21, g34_22, g34_23, g34_24, g34_25, g34_26, g34_27, w34_328, w34_32c, w34_348, w34_34c, keep_kk34.mono (by decide)⟩

end C3.RV32.Sv
