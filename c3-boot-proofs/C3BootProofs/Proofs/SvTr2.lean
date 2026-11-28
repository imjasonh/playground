import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: the timestamp token's `ContentInfo` and `SignedData` version

From 0xB06 to 0xC08: the response's second element is a `ContentInfo` with nothing after it, whose content type is signedData and whose `[0]` holds only a `SEQUENCE`, the `SignedData`, which starts with `INTEGER 3`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTr2b06 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x2E0]
theorem svTr2b06_end : blockEnd sigstoreVerifyCode 0xB06 svTr2b06 = some 0xB0C := by
  simp only [svTr2b06]
  rw [blockEnd, sv_at_b06]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b0a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr2b20 : List BInstr :=
  [.aluImm .add a1 sp 0x425, .aluImm .add a0 sp 0x305, .aluImm .add a2 x0 0xB]
theorem svTr2b20_end : blockEnd sigstoreVerifyCode 0xB20 svTr2b20 = some 0xB2A := by
  simp only [svTr2b20]
  rw [blockEnd, sv_at_b20]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b24]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b28]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr214c : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x1]
theorem svTr214c_end : blockEnd sigstoreVerifyCode 0x14C svTr214c = some 0x14E := by
  simp only [svTr214c]
  rw [blockEnd, sv_at_14c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr2b42 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x300]
theorem svTr2b42_end : blockEnd sigstoreVerifyCode 0xB42 svTr2b42 = some 0xB48 := by
  simp only [svTr2b42]
  rw [blockEnd, sv_at_b42]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b46]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr2b5c : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF841, .aluImm .add a3 x0 0x9]
theorem svTr2b5c_end : blockEnd sigstoreVerifyCode 0xB5C svTr2b5c = some 0xB66 := by
  simp only [svTr2b5c]
  rw [blockEnd, sv_at_b5c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b60]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b64]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr212b8 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x18]
theorem svTr212b8_end : blockEnd sigstoreVerifyCode 0x12B8 svTr212b8 = some 0x12BA := by
  simp only [svTr212b8]
  rw [blockEnd, sv_at_12b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr2b72 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x300, .aluImm .add a2 x0 0xA0]
theorem svTr2b72_end : blockEnd sigstoreVerifyCode 0xB72 svTr2b72 = some 0xB7C := by
  simp only [svTr2b72]
  rw [blockEnd, sv_at_b72]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b76]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b78]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr2b90 : List BInstr :=
  [.aluImm .add a1 sp 0x425, .aluImm .add a0 sp 0x315, .aluImm .add a2 x0 0xB]
theorem svTr2b90_end : blockEnd sigstoreVerifyCode 0xB90 svTr2b90 = some 0xB9A := by
  simp only [svTr2b90]
  rw [blockEnd, sv_at_b90]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b94]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_b98]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr2bb2 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x310]
theorem svTr2bb2_end : blockEnd sigstoreVerifyCode 0xBB2 svTr2bb2 = some 0xBB8 := by
  simp only [svTr2bb2]
  rw [blockEnd, sv_at_bb2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_bb6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr2bcc : List BInstr :=
  [.aluImm .add a1 sp 0x425, .aluImm .add a0 sp 0x325, .aluImm .add a2 x0 0xB]
theorem svTr2bcc_end : blockEnd sigstoreVerifyCode 0xBCC svTr2bcc = some 0xBD6 := by
  simp only [svTr2bcc]
  rw [blockEnd, sv_at_bcc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_bd0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_bd4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr2bee : List BInstr :=
  [.aluImm .add a0 sp 0x320, .aluImm .add a1 x0 0x3]
theorem svTr2bee_end : blockEnd sigstoreVerifyCode 0xBEE svTr2bee = some 0xBF2 := by
  simp only [svTr2bee]
  rw [blockEnd, sv_at_bee]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_bf0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr2bfa : List BInstr :=
  [.aluImm .and a0 a0 0x1, .alu .add (8 : Fin 32) x0 a1]
theorem svTr2bfa_end : blockEnd sigstoreVerifyCode 0xBFA svTr2bfa = some 0xBFE := by
  simp only [svTr2bfa]
  rw [blockEnd, sv_at_bfa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_bfc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr2c02 : List BInstr :=
  [.aluImm .and (8 : Fin 32) (8 : Fin 32) 0x1]
theorem svTr2c02_end : blockEnd sigstoreVerifyCode 0xC02 svTr2c02 = some 0xC04 := by
  simp only [svTr2c02]
  rw [blockEnd, sv_at_c02]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tr2 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 rp rl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xB06 (reg n0))
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
    (w0_2e8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = rp)
    (w0_2ec : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = rl)
    (r_in : SvIn B (rp) (rl).toNat) :
    (¬ (∃ tl2, derElement 0x30 (memBytes M0 (rp) (rl).toNat) = .ok tl2 ∧ ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧ ∃ op13 ol13, derContent ((rp) + BitVec.ofNat 32 tl2.header) (derOid (memBytes M0 ((rp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat)) = .ok (op13, ol13) ∧ ∃ to13, derOid (memBytes M0 ((rp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat) = .ok to13 ∧ (memBytes M0 op13 ol13.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress)) 9) ∧ ∃ tl21, derElement 0xA0 (memBytes M0 (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)).toNat) = .ok tl21 ∧ (((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) = 0) ∧ ∃ tl32, derElement 0x30 (memBytes M0 ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) (BitVec.ofNat 32 tl21.len).toNat) = .ok tl32 ∧ ((BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) = 0) ∧ derIntIsOf M0 (memBytes M0 (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) (BitVec.ofNat 32 tl32.len).toNat) (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) (derElement 2 (memBytes M0 (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) (BitVec.ofNat 32 tl32.len).toNat)) ((BitVec.ofNat 32 0x3).extractLsb' 0 8) = .ok true ∧ ∃ te43, derElement 2 (memBytes M0 (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) (BitVec.ofNat 32 tl32.len).toNat) = .ok te43 ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl2, derElement 0x30 (memBytes M0 (rp) (rl).toNat) = .ok tl2 ∧
    ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧
    ∃ op13 ol13, derContent ((rp) + BitVec.ofNat 32 tl2.header) (derOid (memBytes M0 ((rp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat)) = .ok (op13, ol13) ∧
    ∃ to13, derOid (memBytes M0 ((rp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat) = .ok to13 ∧
    (memBytes M0 op13 ol13.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress)) 9) ∧
    ∃ tl21, derElement 0xA0 (memBytes M0 (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)).toNat) = .ok tl21 ∧
    (((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) = 0) ∧
    ∃ tl32, derElement 0x30 (memBytes M0 ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) (BitVec.ofNat 32 tl21.len).toNat) = .ok tl32 ∧
    ((BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) = 0) ∧
    derIntIsOf M0 (memBytes M0 (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) (BitVec.ofNat 32 tl32.len).toNat) (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) (derElement 2 (memBytes M0 (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) (BitVec.ofNat 32 tl32.len).toNat)) ((BitVec.ofNat 32 0x3).extractLsb' 0 8) = .ok true ∧
    ∃ te43, derElement 2 (memBytes M0 (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) (BitVec.ofNat 32 tl32.len).toNat) = .ok te43 ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xC08 (reg n') ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) + BitVec.ofNat 32 (te43.header + te43.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (BitVec.ofNat 32 tl32.len) - BitVec.ofNat 32 (te43.header + te43.len) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xB06
  obtain ⟨n1, c1, u1⟩ := s0.block svTr2b06 E0.self svTr2b06_end
    ⟨trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0xB0C (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTr2b06 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr2b06, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x2E0 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr2b06, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_2e8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = rp := by rw [m1]; exact w0_2e8
  have w1_2ec : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = rl := by rw [m1]; exact w0_2ec
  -- 0xB0C: sv_seqF
  obtain ⟨n2, c2, s2, sp2, rk2, K2, Ok2, Er2, fr2⟩ := sv_seqF (oc := 0x420) (dc := 0x2E0)
    F E1 s1 sv_at_b0c sv_at_b10 (by decide) (by decide) g1_2 g1_10 g1_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w1_2e8 w1_2ec r_in
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keepL K2 (by decide)
  rw [sv_mb fR1 r_in] at Ok2 Er2
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
  obtain ⟨r2, hr2⟩ : ∃ r, derElement 0x30 (memBytes M0 (rp) (rl).toNat) = r := ⟨_, rfl⟩
  rcases r2 with er2 | tl2
  · obtain ⟨z2, ez2⟩ := Er2 er2 hr2
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x10), (0x2E8, 0x8)] := keep_kk1.trans K2
    clear keep_kk1
    have w2_420 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z2
    have b2_424 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er2 := ez2
    clear w1_2ec w1_2e8 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0xB14: lw
    obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_b14 (off' := 0xB18) (by decide)
      (by rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s3 : St n3.mem SV n3 0xB18 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x10), (0x2E8, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_420 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m3]; exact w2_420
    have b3_424 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er2 := by rw [m3]; exact b2_424
    clear b2_424 w2_420 ez2 z2
    -- 0xB18: lbu
    obtain ⟨n4, d4, u4⟩ := s3.lbu E3.self sv_at_b18 (off' := 0xB1C) (by decide)
    have s4 : St n4.mem SV n4 0xB1C (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
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
    have g4_8 : reg n4 (8 : Fin 32) = (derErrByte er2).zeroExtend 32 := by
      rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g3_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b3_424]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x10), (0x2E8, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m4]; exact w3_420
    have b4_424 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er2 := by rw [m4]; exact b3_424
    clear b3_424 w3_420 g3_9 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    -- 0xB1C: branch, taken
    obtain ⟨n5, d5, u5⟩ := s4.taken E4.self 0x7A4 sv_at_b1c
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
    have g5_8 : reg n5 (8 : Fin 32) = (derErrByte er2).zeroExtend 32 := by rw [u5.regs, g4_8]
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
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x10), (0x2E8, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m5]; exact w4_420
    have b5_424 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er2 := by rw [m5]; exact b4_424
    clear b4_424 w4_420 g4_8 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    exact .inl ⟨(fun ⟨tl2', h0', _⟩ => by rw [hr2] at h0'; cases h0'), sv_fail F E5 s5 t5 (fun x hx => (fR5 x hx).trans (fM x hx).symm) V5 hret g5_2 g5_18 hO g5_3 g5_4 (by rw [g5_8]; sv_code)⟩
  obtain ⟨o0_2, o4_2, o8_2, o12_2, d8_2, d12_2⟩ := Ok2 tl2 hr2
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x10), (0x2E8, 0x8)] := keep_kk1.trans K2
  clear keep_kk1
  have w2_2e8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := d8_2
  have w2_2ec : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := d12_2
  have w2_420 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := o0_2
  have w2_424 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := o4_2
  have w2_428 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := o8_2
  have w2_42c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := o12_2
  clear w1_2ec w1_2e8 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0xB14: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_b14 (off' := 0xB18) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0xB18 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
  have g3_9 : reg n3 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w2_420]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x10), (0x2E8, 0x8)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_2e8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_2e8
  have w3_2ec : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_2ec
  have w3_420 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m3]; exact w2_420
  have w3_424 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m3]; exact w2_424
  have w3_428 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m3]; exact w2_428
  have w3_42c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m3]; exact w2_42c
  clear w2_42c w2_428 w2_424 w2_420 w2_2ec w2_2e8 d12_2 d8_2 o12_2 o8_2 o4_2 o0_2 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 Er2 Ok2 K2 rk2 sp2 s2 c2
  -- 0xB18: lbu
  obtain ⟨n4, d4, u4⟩ := s3.lbu E3.self sv_at_b18 (off' := 0xB1C) (by decide)
  have b3_424 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by
    have h := byte_of_ld w3_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s4 : St n4.mem SV n4 0xB1C (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_9 : reg n4 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u4.regs, upd_ne (by decide) (by decide), g3_9]
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
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x10), (0x2E8, 0x8)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_2e8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_2e8
  have w4_2ec : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_2ec
  have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m4]; exact w3_420
  have w4_424 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m4]; exact w3_424
  have w4_428 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m4]; exact w3_428
  have w4_42c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m4]; exact w3_42c
  have b4_424 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m4]; exact b3_424
  clear w3_42c w3_428 w3_424 w3_420 w3_2ec w3_2e8 g3_9 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0xB1C: branch, not taken
  obtain ⟨n5, d5, u5⟩ := s4.notTaken E4.self 0xB20 sv_at_b1c
    (by decide) (by rw [g4_9, s4.zero]; exact br_beq_f (r_in.ok_ne hr2))
  have s5 : St n5.mem SV n5 0xB20 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
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
  have g5_9 : reg n5 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u5.regs, g4_9]
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
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x10), (0x2E8, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_2e8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_2e8
  have w5_2ec : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_2ec
  have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m5]; exact w4_420
  have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m5]; exact w4_424
  have w5_428 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m5]; exact w4_428
  have w5_42c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m5]; exact w4_42c
  have b5_424 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m5]; exact b4_424
  clear b4_424 w4_42c w4_428 w4_424 w4_420 w4_2ec w4_2e8 g4_8 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 b3_424 u4 d4
  -- 0xB20
  obtain ⟨n6, c6, u6⟩ := s5.block svTr2b20 E5.self svTr2b20_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0xB2A (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svTr2b20 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_9 : reg n6 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by
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
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x305 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTr2b20, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_11 : reg n6 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTr2b20, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_12 : reg n6 a2 = BitVec.ofNat 32 0xB := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTr2b20, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x10), (0x2E8, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_2e8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_2e8
  have w6_2ec : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_2ec
  have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m6]; exact w5_420
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m6]; exact w5_424
  have w6_428 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m6]; exact w5_428
  have w6_42c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m6]; exact w5_42c
  have b6_424 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m6]; exact b5_424
  clear b5_424 w5_42c w5_428 w5_424 w5_420 w5_2ec w5_2e8 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  have b6_425 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by
    have h := byte_of_ld w6_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b6_426 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by
    have h := byte_of_ld w6_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b6_427 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by
    have h := byte_of_ld w6_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0xB2A: memcpy
  obtain ⟨n7, P7, K7, X7⟩ := sv_mc (c := 0x305) (d := 0x425) (N := 0xB) F E6 s6 sv_at_b2a sv_at_b2e
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
  have g7_9 : reg n7 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [P7.regs (9 : Fin 32) (by decide), g6_9]
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
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_2e8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K7.w32 (by decide) (by decide)).trans w6_2e8
  have w7_2ec : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K7.w32 (by decide) (by decide)).trans w6_2ec
  have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := (K7.w32 (by decide) (by decide)).trans w6_420
  have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := (K7.w32 (by decide) (by decide)).trans w6_424
  have w7_428 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := (K7.w32 (by decide) (by decide)).trans w6_428
  have w7_42c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K7.w32 (by decide) (by decide)).trans w6_42c
  have b7_424 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K7.b8 (by decide) (by decide)).trans b6_424
  have b7_425 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K7.b8 (by decide) (by decide)).trans b6_425
  have b7_426 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K7.b8 (by decide) (by decide)).trans b6_426
  have b7_427 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K7.b8 (by decide) (by decide)).trans b6_427
  have w7_308 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (rp) + BitVec.ofNat 32 tl2.header := by
    rw [← w6_428]
    exact ld_cp fun q hq => by
      have := X7 (0x3 + q) (by omega)
      rwa [show 0x305 + (0x3 + q) = 0x308 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w7_30c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = BitVec.ofNat 32 tl2.len := by
    rw [← w6_42c]
    exact ld_cp fun q hq => by
      have := X7 (0x7 + q) (by omega)
      rwa [show 0x305 + (0x7 + q) = 0x30C + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b7_305 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x305) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [show 0x305 = 0x305 + 0x0 from rfl, X7 0x0 (by decide)]; exact b6_425
  have b7_306 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x306) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [show 0x306 = 0x305 + 0x1 from rfl, X7 0x1 (by decide)]; exact b6_426
  have b7_307 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x307) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [show 0x307 = 0x305 + 0x2 from rfl, X7 0x2 (by decide)]; exact b6_427
  clear b6_424 w6_42c w6_428 w6_424 w6_420 w6_2ec w6_2e8 g6_12 g6_11 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0xB32: lw
  obtain ⟨n8, d8, u8⟩ := s7.lw E7.self sv_at_b32 (off' := 0xB36) (by decide)
    (by rw [g7_2, show B + 0x21A0 + 0x2EC = B + 0x21A0 + BitVec.ofNat 32 0x2EC by sv_addr]; exact sv_al F (by decide) (by decide))
  have s8 : St n8.mem SV n8 0xB36 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
  have g8_10 : reg n8 a0 = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x2EC = B + 0x21A0 + BitVec.ofNat 32 0x2EC by sv_addr, w7_2ec]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_2e8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_2e8
  have w8_2ec : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_2ec
  have w8_308 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m8]; exact w7_308
  have w8_30c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = BitVec.ofNat 32 tl2.len := by rw [m8]; exact w7_30c
  have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m8]; exact w7_420
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m8]; exact w7_424
  have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m8]; exact w7_428
  have w8_42c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m8]; exact w7_42c
  have b8_305 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x305) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m8]; exact b7_305
  have b8_306 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x306) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m8]; exact b7_306
  have b8_307 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x307) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m8]; exact b7_307
  have b8_424 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m8]; exact b7_424
  have b8_425 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m8]; exact b7_425
  have b8_426 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m8]; exact b7_426
  have b8_427 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m8]; exact b7_427
  clear b7_307 b7_306 b7_305 w7_30c w7_308 b7_427 b7_426 b7_425 b7_424 w7_42c w7_428 w7_424 w7_420 w7_2ec w7_2e8 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 s7 X7 K7 P7 b6_427 b6_426 b6_425
  -- 0xB36: sw
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sw F E8 s8 sv_at_b36 (off' := 0xB3A) (c := 0x300)
    (by decide) (by rw [g8_2]; sv_addr) (by decide) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg9 (8 : Fin 32), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [rg9 (9 : Fin 32), g8_9]
  have g9_10 : reg n9 a0 = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg9 a0, g8_10]
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
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have w9_2e8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K9.w32 (by decide) (by decide)).trans w8_2e8
  have w9_2ec : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K9.w32 (by decide) (by decide)).trans w8_2ec
  have w9_308 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (rp) + BitVec.ofNat 32 tl2.header := (K9.w32 (by decide) (by decide)).trans w8_308
  have w9_30c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = BitVec.ofNat 32 tl2.len := (K9.w32 (by decide) (by decide)).trans w8_30c
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := (K9.w32 (by decide) (by decide)).trans w8_420
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := (K9.w32 (by decide) (by decide)).trans w8_424
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := (K9.w32 (by decide) (by decide)).trans w8_428
  have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K9.w32 (by decide) (by decide)).trans w8_42c
  have b9_305 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x305) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K9.b8 (by decide) (by decide)).trans b8_305
  have b9_306 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x306) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K9.b8 (by decide) (by decide)).trans b8_306
  have b9_307 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x307) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K9.b8 (by decide) (by decide)).trans b8_307
  have b9_424 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K9.b8 (by decide) (by decide)).trans b8_424
  have b9_425 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K9.b8 (by decide) (by decide)).trans b8_425
  have b9_426 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K9.b8 (by decide) (by decide)).trans b8_426
  have b9_427 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K9.b8 (by decide) (by decide)).trans b8_427
  have w9_300 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [W9, g8_9]
  clear b8_427 b8_426 b8_425 b8_424 b8_307 b8_306 b8_305 w8_42c w8_428 w8_424 w8_420 w8_30c w8_308 w8_2ec w8_2e8 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0xB3A: sb
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sb F E9 s9 sv_at_b3a (off' := 0xB3E) (c := 0x304)
    (by decide) (by rw [g9_2]; sv_addr) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg10 (8 : Fin 32), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [rg10 (9 : Fin 32), g9_9]
  have g10_10 : reg n10 a0 = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg10 a0, g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rg10 (18 : Fin 32), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rg10 (19 : Fin 32), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [rg10 (20 : Fin 32), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [rg10 (21 : Fin 32), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [rg10 (22 : Fin 32), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [rg10 (23 : Fin 32), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [rg10 (24 : Fin 32), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [rg10 (25 : Fin 32), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [rg10 (26 : Fin 32), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [rg10 (27 : Fin 32), g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_2e8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K10.w32 (by decide) (by decide)).trans w9_2e8
  have w10_2ec : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K10.w32 (by decide) (by decide)).trans w9_2ec
  have w10_300 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K10.w32 (by decide) (by decide)).trans w9_300
  have w10_308 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (rp) + BitVec.ofNat 32 tl2.header := (K10.w32 (by decide) (by decide)).trans w9_308
  have w10_30c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = BitVec.ofNat 32 tl2.len := (K10.w32 (by decide) (by decide)).trans w9_30c
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := (K10.w32 (by decide) (by decide)).trans w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := (K10.w32 (by decide) (by decide)).trans w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := (K10.w32 (by decide) (by decide)).trans w9_428
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K10.w32 (by decide) (by decide)).trans w9_42c
  have b10_305 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x305) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K10.b8 (by decide) (by decide)).trans b9_305
  have b10_306 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x306) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K10.b8 (by decide) (by decide)).trans b9_306
  have b10_307 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x307) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K10.b8 (by decide) (by decide)).trans b9_307
  have b10_424 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K10.b8 (by decide) (by decide)).trans b9_424
  have b10_425 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K10.b8 (by decide) (by decide)).trans b9_425
  have b10_426 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K10.b8 (by decide) (by decide)).trans b9_426
  have b10_427 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K10.b8 (by decide) (by decide)).trans b9_427
  have b10_304 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [W10, g9_8, lbu_low]
  clear w9_300 b9_427 b9_426 b9_425 b9_424 b9_307 b9_306 b9_305 w9_42c w9_428 w9_424 w9_420 w9_30c w9_308 w9_2ec w9_2e8 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  have w10_304 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := ld_of_bytes b10_304
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x304 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x305 by sv_addr]; exact b10_305)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x304 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x306 by sv_addr]; exact b10_306)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x304 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x307 by sv_addr]; exact b10_307)
  by_cases hrem : (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0
  rotate_left
  · -- 0xB3E: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x14C sv_at_b3e
      (by decide) (by rw [g10_10, s10.zero]; exact br_bne_t hrem)
    have s11 : St n11.mem SV n11 0x14C (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u11.regs, g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_2e8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_2e8
    have w11_2ec : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_2ec
    have w11_300 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_300
    have w11_304 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_304
    have w11_308 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_308
    have w11_30c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_30c
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_420
    have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_424
    have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_428
    have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_42c
    have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m11]; exact b10_424
    have b11_425 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m11]; exact b10_425
    have b11_426 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m11]; exact b10_426
    have b11_427 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m11]; exact b10_427
    clear b10_304 b10_427 b10_426 b10_425 b10_424 b10_307 b10_306 b10_305 w10_42c w10_428 w10_424 w10_420 w10_30c w10_308 w10_300 w10_2ec w10_2e8 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
    -- 0x14C
    obtain ⟨n12, c12, u12⟩ := s11.block svTr214c E11.self svTr214c_end
      ⟨trivial, trivial⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have s12 : St n12.mem SV n12 0x14E (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have rb12 : ∀ q, reg n12 q = (runBlock svTr214c (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
    have g12_9 : reg n12 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by
      rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
    have g12_10 : reg n12 a0 = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by
      rw [rb12, runBlock_reg _ _ _ a0 s11.zero (by decide), g11_10]
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
      rw [rb12]; simp +decide only [runBlock, BInstr.run, svTr214c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_2e8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_2e8
    have w12_2ec : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_2ec
    have w12_300 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_300
    have w12_304 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_304
    have w12_308 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_308
    have w12_30c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_30c
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_420
    have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_424
    have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_428
    have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_42c
    have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m12]; exact b11_424
    have b12_425 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m12]; exact b11_425
    have b12_426 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m12]; exact b11_426
    have b12_427 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m12]; exact b11_427
    clear b11_427 b11_426 b11_425 b11_424 w11_42c w11_428 w11_424 w11_420 w11_30c w11_308 w11_304 w11_300 w11_2ec w11_2e8 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    -- 0x14E: j
    obtain ⟨n13, d13, u13⟩ := s12.jump E12.self sv_at_14e (off' := 0x7A4) (by decide)
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
    have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u13.regs, g12_8]
    have g13_9 : reg n13 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u13.regs, g12_9]
    have g13_10 : reg n13 a0 = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u13.regs, g12_10]
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
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_2e8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m13]; exact w12_2e8
    have w13_2ec : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m13]; exact w12_2ec
    have w13_300 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_300
    have w13_304 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_304
    have w13_308 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_308
    have w13_30c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_30c
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_420
    have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_424
    have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_428
    have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_42c
    have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m13]; exact b12_424
    have b13_425 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m13]; exact b12_425
    have b13_426 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m13]; exact b12_426
    have b13_427 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m13]; exact b12_427
    clear b12_427 b12_426 b12_425 b12_424 w12_42c w12_428 w12_424 w12_420 w12_30c w12_308 w12_304 w12_300 w12_2ec w12_2e8 g12_8 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
    exact .inl ⟨(fun ⟨tl2', h0', h1', _⟩ => by rw [hr2] at h0'; cases h0'; exact hrem h1'), sv_fail F E13 s13 t13 (fun x hx => (fR13 x hx).trans (fM x hx).symm) V13 hret g13_2 g13_18 hO g13_3 g13_4 (by rw [g13_8]; sv_code)⟩
  -- 0xB3E: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0xB42 sv_at_b3e
    (by decide) (by rw [g10_10, s10.zero]; exact br_bne_f hrem)
  have s11 : St n11.mem SV n11 0xB42 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u11.regs, g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u11.regs, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_2e8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_2e8
  have w11_2ec : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_2ec
  have w11_300 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_300
  have w11_304 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_304
  have w11_308 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_308
  have w11_30c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_30c
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_42c
  have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m11]; exact b10_424
  have b11_425 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m11]; exact b10_425
  have b11_426 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m11]; exact b10_426
  have b11_427 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m11]; exact b10_427
  clear b10_304 b10_427 b10_426 b10_425 b10_424 b10_307 b10_306 b10_305 w10_42c w10_428 w10_424 w10_420 w10_30c w10_308 w10_300 w10_2ec w10_2e8 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0xB42
  obtain ⟨n12, c12, u12⟩ := s11.block svTr2b42 E11.self svTr2b42_end
    ⟨trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0xB48 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svTr2b42 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_8 : reg n12 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by
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
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svTr2b42, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svTr2b42, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_2e8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_2e8
  have w12_2ec : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_2ec
  have w12_300 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_300
  have w12_304 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_304
  have w12_308 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_308
  have w12_30c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_30c
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_42c
  have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m12]; exact b11_424
  have b12_425 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m12]; exact b11_425
  have b12_426 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m12]; exact b11_426
  have b12_427 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m12]; exact b11_427
  clear b11_427 b11_426 b11_425 b11_424 w11_42c w11_428 w11_424 w11_420 w11_30c w11_308 w11_304 w11_300 w11_2ec w11_2e8 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11 w10_304
  -- 0xB48: sv_oidF
  obtain ⟨n13, c13, s13, sp13, rk13, K13, A13, Ok13, Er13, fr13⟩ := sv_oidF (oc := 0x420) (dc := 0x300)
    F E12 s12 sv_at_b48 sv_at_b4c (by decide) (by decide) g12_2 g12_10 g12_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w12_308 w12_30c (r_in.contentW hr2)
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keepL K13 (by decide)
  rw [sv_mb fR12 (r_in.contentW hr2)] at A13 Ok13 Er13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rk13 sp (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk13 (3 : Fin 32) (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk13 (4 : Fin 32) (by decide) (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk13 (8 : Fin 32) (by decide) (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [rk13 (9 : Fin 32) (by decide) (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rk13 (18 : Fin 32) (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rk13 (19 : Fin 32) (by decide) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [rk13 (20 : Fin 32) (by decide) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [rk13 (21 : Fin 32) (by decide) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [rk13 (22 : Fin 32) (by decide) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [rk13 (23 : Fin 32) (by decide) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [rk13 (24 : Fin 32) (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [rk13 (25 : Fin 32) (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [rk13 (26 : Fin 32) (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [rk13 (27 : Fin 32) (by decide) (by decide), g12_27]
  obtain ⟨r13, hr13⟩ : ∃ r, derContent ((rp) + BitVec.ofNat 32 tl2.header) (derOid (memBytes M0 ((rp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat)) = r := ⟨_, rfl⟩
  rcases r13 with er13 | ⟨op13, ol13⟩
  · obtain ⟨z13, ez13⟩ := Er13 er13 hr13
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := keep_kk12.trans K13
    clear keep_kk12
    have w13_2e8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K13.w32 (by decide) (by decide)).trans w12_2e8
    have w13_2ec : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K13.w32 (by decide) (by decide)).trans w12_2ec
    have w13_300 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K13.w32 (by decide) (by decide)).trans w12_300
    have w13_304 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K13.w32 (by decide) (by decide)).trans w12_304
    have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := (K13.w32 (by decide) (by decide)).trans w12_428
    have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K13.w32 (by decide) (by decide)).trans w12_42c
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z13
    have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er13 := ez13
    clear b12_427 b12_426 b12_425 b12_424 w12_42c w12_428 w12_424 w12_420 w12_30c w12_308 w12_304 w12_300 w12_2ec w12_2e8 g12_11 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
    -- 0xB50: lw
    obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_b50 (off' := 0xB54) (by decide)
      (by rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s14 : St n14.mem SV n14 0xB54 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
    have t14 : Steps n0 n14 := t13.trans (.single d14)
    have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
    have E14 : SvCode n14.mem := E13.fr F fr14
    have V14 : SvSaves B n14.mem v := V13.same m14
    have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
    have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
    have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
    have g14_8 : reg n14 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_8]
    have g14_9 : reg n14 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u14.regs, upd_ne (by decide) (by decide), g13_9]
    have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, upd_ne (by decide) (by decide), g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_19]
    have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_20]
    have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_21]
    have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_22]
    have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_23]
    have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = x27 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_27]
    have g14_10 : reg n14 a0 = 0 := by
      rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w13_420]
    have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m14]; exact keep_kk13
    clear keep_kk13
    have w14_2e8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_2e8
    have w14_2ec : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_2ec
    have w14_300 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_300
    have w14_304 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_304
    have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m14]; exact w13_420
    have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_428
    have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_42c
    have b14_424 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er13 := by rw [m14]; exact b13_424
    clear b13_424 w13_420 w13_42c w13_428 w13_304 w13_300 w13_2ec w13_2e8 ez13 z13
    -- 0xB54: branch, taken
    obtain ⟨n15, d15, u15⟩ := s14.taken E14.self 0x12AA sv_at_b54
      (by decide) (by rw [g14_10, s14.zero]; rfl)
    have s15 : St n15.mem SV n15 0x12AA (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
    have t15 : Steps n0 n15 := t14.trans (.single d15)
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.same m15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
    have g15_8 : reg n15 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u15.regs, g14_8]
    have g15_9 : reg n15 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u15.regs, g14_9]
    have g15_10 : reg n15 a0 = 0 := by rw [u15.regs, g14_10]
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
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m15]; exact keep_kk14
    clear keep_kk14
    have w15_2e8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_2e8
    have w15_2ec : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_2ec
    have w15_300 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_300
    have w15_304 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_304
    have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m15]; exact w14_420
    have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_428
    have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_42c
    have b15_424 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er13 := by rw [m15]; exact b14_424
    clear b14_424 w14_42c w14_428 w14_420 w14_304 w14_300 w14_2ec w14_2e8 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
    -- 0x12AA: lbu
    obtain ⟨n16, d16, u16⟩ := s15.lbu E15.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s16 : St n16.mem SV n16 0x12AE (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
    have g16_9 : reg n16 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
    have g16_10 : reg n16 a0 = 0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_10]
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
    have g16_8 : reg n16 (8 : Fin 32) = (derErrByte er13).zeroExtend 32 := by
      rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g15_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b15_424]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_2e8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_2e8
    have w16_2ec : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_2ec
    have w16_300 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m16]; exact w15_300
    have w16_304 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m16]; exact w15_304
    have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m16]; exact w15_420
    have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m16]; exact w15_428
    have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m16]; exact w15_42c
    have b16_424 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er13 := by rw [m16]; exact b15_424
    clear b15_424 w15_42c w15_428 w15_420 w15_304 w15_300 w15_2ec w15_2e8 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
    -- 0x12AE: j
    obtain ⟨n17, d17, u17⟩ := s16.jump E16.self sv_at_12ae (off' := 0x7A4) (by decide)
      (by rw [s16.pc]; decide)
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
    have g17_8 : reg n17 (8 : Fin 32) = (derErrByte er13).zeroExtend 32 := by rw [u17.regs, g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u17.regs, g16_9]
    have g17_10 : reg n17 a0 = 0 := by rw [u17.regs, g16_10]
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
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_2e8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m17]; exact w16_2e8
    have w17_2ec : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m17]; exact w16_2ec
    have w17_300 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m17]; exact w16_300
    have w17_304 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m17]; exact w16_304
    have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m17]; exact w16_420
    have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m17]; exact w16_428
    have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m17]; exact w16_42c
    have b17_424 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er13 := by rw [m17]; exact b16_424
    clear b16_424 w16_42c w16_428 w16_420 w16_304 w16_300 w16_2ec w16_2e8 g16_8 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_10 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    exact .inl ⟨(fun ⟨tl2', h0', h1', op13', ol13', h2', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'), sv_fail F E17 s17 t17 (fun x hx => (fR17 x hx).trans (fM x hx).symm) V17 hret g17_2 g17_18 hO g17_3 g17_4 (by rw [g17_8]; sv_code)⟩
  obtain ⟨to13, ht13, -, -⟩ := oid_ok_content hr13
  obtain ⟨p0_13, p4_13⟩ := Ok13 op13 ol13 hr13
  obtain ⟨d8_13, d12_13⟩ := A13 to13 (derOid_ok_elem ht13)
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := keep_kk12.trans K13
  clear keep_kk12
  have w13_2e8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K13.w32 (by decide) (by decide)).trans w12_2e8
  have w13_2ec : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K13.w32 (by decide) (by decide)).trans w12_2ec
  have w13_300 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K13.w32 (by decide) (by decide)).trans w12_300
  have w13_304 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K13.w32 (by decide) (by decide)).trans w12_304
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := (K13.w32 (by decide) (by decide)).trans w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K13.w32 (by decide) (by decide)).trans w12_42c
  have w13_308 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = ((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len) := d8_13
  have w13_30c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len) := d12_13
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op13 := p0_13
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol13 := p4_13
  clear b12_427 b12_426 b12_425 b12_424 w12_42c w12_428 w12_424 w12_420 w12_30c w12_308 w12_304 w12_300 w12_2ec w12_2e8 g12_11 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0xB50: lw
  obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_b50 (off' := 0xB54) (by decide)
    (by rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s14 : St n14.mem SV n14 0xB54 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u14.regs, upd_ne (by decide) (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, upd_ne (by decide) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_27]
  have g14_10 : reg n14 a0 = op13 := by
    rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w13_420]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_2e8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_2e8
  have w14_2ec : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_2ec
  have w14_300 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_300
  have w14_304 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_304
  have w14_308 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = ((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len) := by rw [m14]; exact w13_308
  have w14_30c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len) := by rw [m14]; exact w13_30c
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op13 := by rw [m14]; exact w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol13 := by rw [m14]; exact w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_42c
  clear w13_424 w13_420 w13_30c w13_308 w13_42c w13_428 w13_304 w13_300 w13_2ec w13_2e8 d12_13 d8_13 p4_13 p0_13 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 Er13 Ok13 A13 K13 rk13 sp13 s13 c13
  -- 0xB54: branch, not taken
  obtain ⟨n15, d15, u15⟩ := s14.notTaken E14.self 0xB58 sv_at_b54
    (by decide) (by rw [g14_10, s14.zero]; exact br_beq_f (((r_in.contentW hr2).oidIn hr13).pos_ne))
  have s15 : St n15.mem SV n15 0xB58 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u15.regs, g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u15.regs, g14_9]
  have g15_10 : reg n15 a0 = op13 := by rw [u15.regs, g14_10]
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
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_2e8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_2e8
  have w15_2ec : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_2ec
  have w15_300 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_300
  have w15_304 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_304
  have w15_308 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = ((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len) := by rw [m15]; exact w14_308
  have w15_30c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len) := by rw [m15]; exact w14_30c
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op13 := by rw [m15]; exact w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol13 := by rw [m15]; exact w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_42c
  clear w14_42c w14_428 w14_424 w14_420 w14_30c w14_308 w14_304 w14_300 w14_2ec w14_2e8 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0xB58: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_b58 (off' := 0xB5C) (by decide)
    (by rw [g15_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s16 : St n16.mem SV n16 0xB5C (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
  have g16_10 : reg n16 a0 = op13 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_10]
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
  have g16_11 : reg n16 a1 = ol13 := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w15_424]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_2e8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_2e8
  have w16_2ec : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_2ec
  have w16_300 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m16]; exact w15_300
  have w16_304 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m16]; exact w15_304
  have w16_308 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = ((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len) := by rw [m16]; exact w15_308
  have w16_30c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len) := by rw [m16]; exact w15_30c
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op13 := by rw [m16]; exact w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol13 := by rw [m16]; exact w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m16]; exact w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m16]; exact w15_42c
  clear w15_42c w15_428 w15_424 w15_420 w15_30c w15_308 w15_304 w15_300 w15_2ec w15_2e8 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0xB5C
  obtain ⟨n17, c17, u17⟩ := s16.block svTr2b5c E16.self svTr2b5c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0xB66 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svTr2b5c (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_8 : reg n17 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_10 : reg n17 a0 = op13 := by
    rw [rb17, runBlock_reg _ _ _ a0 s16.zero (by decide), g16_10]
  have g17_11 : reg n17 a1 = ol13 := by
    rw [rb17, runBlock_reg _ _ _ a1 s16.zero (by decide), g16_11]
  have g17_18 : reg n17 (18 : Fin 32) = out := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by
    rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by
    rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = x27 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 (img% svConstCmsAddress) := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svTr2b5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_11, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_13 : reg n17 a3 = BitVec.ofNat 32 0x9 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svTr2b5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_11, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_2e8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m17]; exact w16_2e8
  have w17_2ec : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m17]; exact w16_2ec
  have w17_300 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m17]; exact w16_300
  have w17_304 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m17]; exact w16_304
  have w17_308 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = ((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len) := by rw [m17]; exact w16_308
  have w17_30c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len) := by rw [m17]; exact w16_30c
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op13 := by rw [m17]; exact w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol13 := by rw [m17]; exact w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m17]; exact w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m17]; exact w16_42c
  clear w16_42c w16_428 w16_424 w16_420 w16_30c w16_308 w16_304 w16_300 w16_2ec w16_2e8 g16_11 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0xB66: sv_sneF
  obtain ⟨n18, c18, s18, rk18, a0_18, K18, fr18⟩ := sv_sneF (pl := ol13.toNat) (ql := 9)
    F E17 s17 sv_at_b66 sv_at_b6a (by decide) (by decide) g17_2
    g17_10 (by rw [g17_11, ofNat_toNat_self]) g17_12 g17_13 (.inl ((r_in.contentW hr2).oidIn hr13)) (.inr ⟨by decide, by decide⟩)
  have t18 : Steps n0 n18 := t17.trans c18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keepL K18 (by decide)
  rw [sv_mbRo FW fR17 (.inl ((r_in.contentW hr2).oidIn hr13)), sv_mbRo FW fR17 (.inr ⟨by decide, by decide⟩)] at a0_18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [rk18 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk18 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk18 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk18 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [rk18 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [rk18 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [rk18 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [rk18 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [rk18 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [rk18 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [rk18 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [rk18 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [rk18 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [rk18 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [rk18 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := keep_kk17.trans K18
  clear keep_kk17
  have w18_2e8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K18.w32 (by decide) (by decide)).trans w17_2e8
  have w18_2ec : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K18.w32 (by decide) (by decide)).trans w17_2ec
  have w18_300 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K18.w32 (by decide) (by decide)).trans w17_300
  have w18_304 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K18.w32 (by decide) (by decide)).trans w17_304
  have w18_308 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = ((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len) := (K18.w32 (by decide) (by decide)).trans w17_308
  have w18_30c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len) := (K18.w32 (by decide) (by decide)).trans w17_30c
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op13 := (K18.w32 (by decide) (by decide)).trans w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol13 := (K18.w32 (by decide) (by decide)).trans w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := (K18.w32 (by decide) (by decide)).trans w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K18.w32 (by decide) (by decide)).trans w17_42c
  clear w17_42c w17_428 w17_424 w17_420 w17_30c w17_308 w17_304 w17_300 w17_2ec w17_2e8 g17_13 g17_12 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_11 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  by_cases hsd : memBytes M0 op13 ol13.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress)) 9
  rotate_left
  · have g18_10 : reg n18 a0 = BitVec.ofNat 32 1 := by rw [a0_18, ite_eq_right hsd]; rfl
    -- 0xB6E: branch, taken
    obtain ⟨n19, d19, u19⟩ := s18.taken E18.self 0x12B8 sv_at_b6e
      (by decide) (by rw [g18_10, s18.zero]; decide)
    have s19 : St n19.mem SV n19 0x12B8 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
    have g19_8 : reg n19 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u19.regs, g18_8]
    have g19_9 : reg n19 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u19.regs, g18_9]
    have g19_10 : reg n19 a0 = BitVec.ofNat 32 0x1 := by rw [u19.regs, g18_10]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [u19.regs, g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [u19.regs, g18_27]
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_2e8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m19]; exact w18_2e8
    have w19_2ec : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m19]; exact w18_2ec
    have w19_300 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m19]; exact w18_300
    have w19_304 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m19]; exact w18_304
    have w19_308 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = ((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len) := by rw [m19]; exact w18_308
    have w19_30c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len) := by rw [m19]; exact w18_30c
    have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op13 := by rw [m19]; exact w18_420
    have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol13 := by rw [m19]; exact w18_424
    have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m19]; exact w18_428
    have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m19]; exact w18_42c
    clear w18_42c w18_428 w18_424 w18_420 w18_30c w18_308 w18_304 w18_300 w18_2ec w18_2e8 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 K18 a0_18 rk18 s18 c18
    -- 0x12B8
    obtain ⟨n20, c20, u20⟩ := s19.block svTr212b8 E19.self svTr212b8_end
      ⟨trivial, trivial⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have s20 : St n20.mem SV n20 0x12BA (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have rb20 : ∀ q, reg n20 q = (runBlock svTr212b8 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
    have g20_9 : reg n20 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by
      rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
    have g20_10 : reg n20 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb20, runBlock_reg _ _ _ a0 s19.zero (by decide), g19_10]
    have g20_18 : reg n20 (18 : Fin 32) = out := by
      rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by
      rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
    have g20_20 : reg n20 (20 : Fin 32) = x20 := by
      rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
    have g20_21 : reg n20 (21 : Fin 32) = x21 := by
      rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = x22 := by
      rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = x23 := by
      rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = x24 := by
      rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = x25 := by
      rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = x26 := by
      rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = x27 := by
      rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
    have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb20]; simp +decide only [runBlock, BInstr.run, svTr212b8, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_2e8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_2e8
    have w20_2ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_2ec
    have w20_300 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m20]; exact w19_300
    have w20_304 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m20]; exact w19_304
    have w20_308 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = ((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len) := by rw [m20]; exact w19_308
    have w20_30c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len) := by rw [m20]; exact w19_30c
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op13 := by rw [m20]; exact w19_420
    have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol13 := by rw [m20]; exact w19_424
    have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m20]; exact w19_428
    have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m20]; exact w19_42c
    clear w19_42c w19_428 w19_424 w19_420 w19_30c w19_308 w19_304 w19_300 w19_2ec w19_2e8 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19 g18_10
    -- 0x12BA: j
    obtain ⟨n21, d21, u21⟩ := s20.jump E20.self sv_at_12ba (off' := 0x7A4) (by decide)
      (by rw [s20.pc]; decide)
    have s21 : St n21.mem SV n21 0x7A4 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
    have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u21.regs, g20_8]
    have g21_9 : reg n21 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u21.regs, g20_9]
    have g21_10 : reg n21 a0 = BitVec.ofNat 32 0x1 := by rw [u21.regs, g20_10]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [u21.regs, g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, g20_27]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_2e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_2e8
    have w21_2ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_2ec
    have w21_300 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m21]; exact w20_300
    have w21_304 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m21]; exact w20_304
    have w21_308 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = ((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len) := by rw [m21]; exact w20_308
    have w21_30c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len) := by rw [m21]; exact w20_30c
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op13 := by rw [m21]; exact w20_420
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol13 := by rw [m21]; exact w20_424
    have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m21]; exact w20_428
    have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m21]; exact w20_42c
    clear w20_42c w20_428 w20_424 w20_420 w20_30c w20_308 w20_304 w20_300 w20_2ec w20_2e8 g20_8 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
    exact .inl ⟨(fun ⟨tl2', h0', h1', op13', ol13', h2', to13', h3', h4', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [ht13] at h3'; cases h3'; exact hsd h4'), sv_fail F E21 s21 t21 (fun x hx => (fR21 x hx).trans (fM x hx).symm) V21 hret g21_2 g21_18 hO g21_3 g21_4 (by rw [g21_8]; sv_code)⟩
  have g18_10 : reg n18 a0 = BitVec.ofNat 32 0 := by rw [a0_18, ite_eq_left hsd]; rfl
  -- 0xB6E: branch, not taken
  obtain ⟨n19, d19, u19⟩ := s18.notTaken E18.self 0xB72 sv_at_b6e
    (by decide) (by rw [g18_10, s18.zero]; decide)
  have s19 : St n19.mem SV n19 0xB72 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u19.regs, g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [u19.regs, g18_9]
  have g19_10 : reg n19 a0 = BitVec.ofNat 32 0x0 := by rw [u19.regs, g18_10]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [u19.regs, g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [u19.regs, g18_27]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_2e8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m19]; exact w18_2e8
  have w19_2ec : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m19]; exact w18_2ec
  have w19_300 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m19]; exact w18_300
  have w19_304 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m19]; exact w18_304
  have w19_308 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = ((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len) := by rw [m19]; exact w18_308
  have w19_30c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len) := by rw [m19]; exact w18_30c
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op13 := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol13 := by rw [m19]; exact w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m19]; exact w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m19]; exact w18_42c
  clear w18_42c w18_428 w18_424 w18_420 w18_30c w18_308 w18_304 w18_300 w18_2ec w18_2e8 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 K18 a0_18 rk18 s18 c18
  -- 0xB72
  obtain ⟨n20, c20, u20⟩ := s19.block svTr2b72 E19.self svTr2b72_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0xB7C (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svTr2b72 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by
    rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = x24 := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svTr2b72, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_11 : reg n20 a1 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svTr2b72, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_12 : reg n20 a2 = BitVec.ofNat 32 0xA0 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svTr2b72, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_2e8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_2e8
  have w20_2ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_2ec
  have w20_300 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m20]; exact w19_300
  have w20_304 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m20]; exact w19_304
  have w20_308 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = ((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len) := by rw [m20]; exact w19_308
  have w20_30c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len) := by rw [m20]; exact w19_30c
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op13 := by rw [m20]; exact w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol13 := by rw [m20]; exact w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m20]; exact w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m20]; exact w19_42c
  clear w19_42c w19_428 w19_424 w19_420 w19_30c w19_308 w19_304 w19_300 w19_2ec w19_2e8 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19 g18_10
  -- 0xB7C: sv_nestF
  obtain ⟨n21, c21, s21, sp21, rk21, K21, Ok21, Er21, fr21⟩ := sv_nestF (oc := 0x420) (dc := 0x300)
    F E20 s20 sv_at_b7c sv_at_b80 (by decide) (by decide) g20_2 g20_10 g20_11 g20_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w20_308 w20_30c ((r_in.contentW hr2).restW (derOid_ok_elem ht13))
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keepL K21 (by decide)
  rw [sv_mb fR20 ((r_in.contentW hr2).restW (derOid_ok_elem ht13))] at Ok21 Er21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rk21 sp (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk21 (3 : Fin 32) (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk21 (4 : Fin 32) (by decide) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk21 (8 : Fin 32) (by decide) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = (rp) + BitVec.ofNat 32 tl2.header := by rw [rk21 (9 : Fin 32) (by decide) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rk21 (18 : Fin 32) (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rk21 (19 : Fin 32) (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [rk21 (20 : Fin 32) (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [rk21 (21 : Fin 32) (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [rk21 (22 : Fin 32) (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [rk21 (23 : Fin 32) (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [rk21 (24 : Fin 32) (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [rk21 (25 : Fin 32) (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [rk21 (26 : Fin 32) (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [rk21 (27 : Fin 32) (by decide) (by decide), g20_27]
  obtain ⟨r21, hr21⟩ : ∃ r, derElement 0xA0 (memBytes M0 (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)).toNat) = r := ⟨_, rfl⟩
  rcases r21 with er21 | tl21
  · obtain ⟨z21, ez21⟩ := Er21 er21 hr21
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8)] := keep_kk20.trans K21
    clear keep_kk20
    have w21_2e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K21.w32 (by decide) (by decide)).trans w20_2e8
    have w21_2ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K21.w32 (by decide) (by decide)).trans w20_2ec
    have w21_300 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K21.w32 (by decide) (by decide)).trans w20_300
    have w21_304 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K21.w32 (by decide) (by decide)).trans w20_304
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z21
    have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := ez21
    clear w20_42c w20_428 w20_424 w20_420 w20_30c w20_308 w20_304 w20_300 w20_2ec w20_2e8 g20_12 g20_11 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
    -- 0xB84: lw
    obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_b84 (off' := 0xB88) (by decide)
      (by rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s22 : St n22.mem SV n22 0xB88 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = x24 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
    have g22_9 : reg n22 (9 : Fin 32) = 0 := by
      rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w21_420]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_2e8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m22]; exact w21_2e8
    have w22_2ec : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m22]; exact w21_2ec
    have w22_300 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m22]; exact w21_300
    have w22_304 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m22]; exact w21_304
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m22]; exact w21_420
    have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := by rw [m22]; exact b21_424
    clear b21_424 w21_420 w21_304 w21_300 w21_2ec w21_2e8 ez21 z21
    -- 0xB88: lbu
    obtain ⟨n23, d23, u23⟩ := s22.lbu E22.self sv_at_b88 (off' := 0xB8C) (by decide)
    have s23 : St n23.mem SV n23 0xB8C (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
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
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
    have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = x24 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
    have g23_8 : reg n23 (8 : Fin 32) = (derErrByte er21).zeroExtend 32 := by
      rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g22_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b22_424]
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_2e8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m23]; exact w22_2e8
    have w23_2ec : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m23]; exact w22_2ec
    have w23_300 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m23]; exact w22_300
    have w23_304 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m23]; exact w22_304
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m23]; exact w22_420
    have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := by rw [m23]; exact b22_424
    clear b22_424 w22_420 w22_304 w22_300 w22_2ec w22_2e8 g22_9 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    -- 0xB8C: branch, taken
    obtain ⟨n24, d24, u24⟩ := s23.taken E23.self 0x7A4 sv_at_b8c
      (by decide) (by rw [g23_9, s23.zero]; rfl)
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
    have g24_8 : reg n24 (8 : Fin 32) = (derErrByte er21).zeroExtend 32 := by rw [u24.regs, g23_8]
    have g24_9 : reg n24 (9 : Fin 32) = 0 := by rw [u24.regs, g23_9]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = x24 := by rw [u24.regs, g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [u24.regs, g23_27]
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_2e8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_2e8
    have w24_2ec : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_2ec
    have w24_300 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m24]; exact w23_300
    have w24_304 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m24]; exact w23_304
    have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m24]; exact w23_420
    have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er21 := by rw [m24]; exact b23_424
    clear b23_424 w23_420 w23_304 w23_300 w23_2ec w23_2e8 g23_8 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
    exact .inl ⟨(fun ⟨tl2', h0', h1', op13', ol13', h2', to13', h3', h4', tl21', h5', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [ht13] at h3'; cases h3'; rw [hr21] at h5'; cases h5'), sv_fail F E24 s24 t24 (fun x hx => (fR24 x hx).trans (fM x hx).symm) V24 hret g24_2 g24_18 hO g24_3 g24_4 (by rw [g24_8]; sv_code)⟩
  obtain ⟨o0_21, o4_21, o8_21, o12_21, d8_21, d12_21⟩ := Ok21 tl21 hr21
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8)] := keep_kk20.trans K21
  clear keep_kk20
  have w21_2e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K21.w32 (by decide) (by decide)).trans w20_2e8
  have w21_2ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K21.w32 (by decide) (by decide)).trans w20_2ec
  have w21_300 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K21.w32 (by decide) (by decide)).trans w20_300
  have w21_304 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K21.w32 (by decide) (by decide)).trans w20_304
  have w21_308 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := d8_21
  have w21_30c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := d12_21
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := o0_21
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := o4_21
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := o8_21
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := o12_21
  clear w20_42c w20_428 w20_424 w20_420 w20_30c w20_308 w20_304 w20_300 w20_2ec w20_2e8 g20_12 g20_11 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0xB84: lw
  obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_b84 (off' := 0xB88) (by decide)
    (by rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s22 : St n22.mem SV n22 0xB88 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = x24 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
  have g22_9 : reg n22 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by
    rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g21_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w21_420]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_2e8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m22]; exact w21_2e8
  have w22_2ec : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m22]; exact w21_2ec
  have w22_300 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m22]; exact w21_300
  have w22_304 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m22]; exact w21_304
  have w22_308 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m22]; exact w21_308
  have w22_30c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m22]; exact w21_30c
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m22]; exact w21_42c
  clear w21_42c w21_428 w21_424 w21_420 w21_30c w21_308 w21_304 w21_300 w21_2ec w21_2e8 d12_21 d8_21 o12_21 o8_21 o4_21 o0_21 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 Er21 Ok21 K21 rk21 sp21 s21 c21
  -- 0xB88: lbu
  obtain ⟨n23, d23, u23⟩ := s22.lbu E22.self sv_at_b88 (off' := 0xB8C) (by decide)
  have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by
    have h := byte_of_ld w22_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s23 : St n23.mem SV n23 0xB8C (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_9 : reg n23 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = x24 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_8 : reg n23 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b22_424]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_2e8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m23]; exact w22_2e8
  have w23_2ec : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m23]; exact w22_2ec
  have w23_300 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m23]; exact w22_300
  have w23_304 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m23]; exact w22_304
  have w23_308 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m23]; exact w22_308
  have w23_30c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m23]; exact w22_30c
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m23]; exact w22_42c
  have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m23]; exact b22_424
  clear w22_42c w22_428 w22_424 w22_420 w22_30c w22_308 w22_304 w22_300 w22_2ec w22_2e8 g22_9 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0xB8C: branch, not taken
  obtain ⟨n24, d24, u24⟩ := s23.notTaken E23.self 0xB90 sv_at_b8c
    (by decide) (by rw [g23_9, s23.zero]; exact br_beq_f (((r_in.contentW hr2).restW (derOid_ok_elem ht13)).ok_ne hr21))
  have s24 : St n24.mem SV n24 0xB90 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [u24.regs, g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [u24.regs, g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = x24 := by rw [u24.regs, g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [u24.regs, g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_2e8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_2e8
  have w24_2ec : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_2ec
  have w24_300 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m24]; exact w23_300
  have w24_304 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m24]; exact w23_304
  have w24_308 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m24]; exact w23_308
  have w24_30c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m24]; exact w23_30c
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m24]; exact w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m24]; exact w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m24]; exact w23_42c
  have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m24]; exact b23_424
  clear b23_424 w23_42c w23_428 w23_424 w23_420 w23_30c w23_308 w23_304 w23_300 w23_2ec w23_2e8 g23_8 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 b22_424 u23 d23
  -- 0xB90
  obtain ⟨n25, c25, u25⟩ := s24.block svTr2b90 E24.self svTr2b90_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0xB9A (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svTr2b90 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by
    rw [rb25, runBlock_reg _ _ _ sp s24.zero (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb25, runBlock_reg _ _ _ (3 : Fin 32) s24.zero (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb25, runBlock_reg _ _ _ (4 : Fin 32) s24.zero (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by
    rw [rb25, runBlock_reg _ _ _ (18 : Fin 32) s24.zero (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by
    rw [rb25, runBlock_reg _ _ _ (19 : Fin 32) s24.zero (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by
    rw [rb25, runBlock_reg _ _ _ (20 : Fin 32) s24.zero (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by
    rw [rb25, runBlock_reg _ _ _ (21 : Fin 32) s24.zero (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by
    rw [rb25, runBlock_reg _ _ _ (22 : Fin 32) s24.zero (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by
    rw [rb25, runBlock_reg _ _ _ (23 : Fin 32) s24.zero (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = x24 := by
    rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by
    rw [rb25, runBlock_reg _ _ _ (25 : Fin 32) s24.zero (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = x27 := by
    rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0x315 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svTr2b90, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svTr2b90, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_12 : reg n25 a2 = BitVec.ofNat 32 0xB := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svTr2b90, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_2e8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m25]; exact w24_2e8
  have w25_2ec : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m25]; exact w24_2ec
  have w25_300 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m25]; exact w24_300
  have w25_304 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m25]; exact w24_304
  have w25_308 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m25]; exact w24_308
  have w25_30c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m25]; exact w24_30c
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m25]; exact w24_420
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m25]; exact w24_424
  have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m25]; exact w24_428
  have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m25]; exact w24_42c
  have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m25]; exact b24_424
  clear b24_424 w24_42c w24_428 w24_424 w24_420 w24_30c w24_308 w24_304 w24_300 w24_2ec w24_2e8 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by
    have h := byte_of_ld w25_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by
    have h := byte_of_ld w25_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by
    have h := byte_of_ld w25_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0xB9A: memcpy
  obtain ⟨n26, P26, K26, X26⟩ := sv_mc (c := 0x315) (d := 0x425) (N := 0xB) F E25 s25 sv_at_b9a sv_at_b9e
    (by decide) (by decide) g25_2 g25_10 g25_11 g25_12
    (by decide) (by decide) (by decide)
  have s26 := P26.st
  have fr26 := P26.fr
  have t26 : Steps n0 n26 := t25.trans P26.steps
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [P26.regs sp (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P26.regs (3 : Fin 32) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P26.regs (4 : Fin 32) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [P26.regs (8 : Fin 32) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [P26.regs (9 : Fin 32) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [P26.regs (18 : Fin 32) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [P26.regs (19 : Fin 32) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [P26.regs (20 : Fin 32) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [P26.regs (21 : Fin 32) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [P26.regs (22 : Fin 32) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [P26.regs (23 : Fin 32) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [P26.regs (24 : Fin 32) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [P26.regs (25 : Fin 32) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [P26.regs (26 : Fin 32) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [P26.regs (27 : Fin 32) (by decide), g25_27]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB)] := keep_kk25.trans K26.toL
  clear keep_kk25
  have w26_2e8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K26.w32 (by decide) (by decide)).trans w25_2e8
  have w26_2ec : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K26.w32 (by decide) (by decide)).trans w25_2ec
  have w26_300 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K26.w32 (by decide) (by decide)).trans w25_300
  have w26_304 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K26.w32 (by decide) (by decide)).trans w25_304
  have w26_308 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K26.w32 (by decide) (by decide)).trans w25_308
  have w26_30c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K26.w32 (by decide) (by decide)).trans w25_30c
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K26.w32 (by decide) (by decide)).trans w25_420
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := (K26.w32 (by decide) (by decide)).trans w25_424
  have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K26.w32 (by decide) (by decide)).trans w25_428
  have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := (K26.w32 (by decide) (by decide)).trans w25_42c
  have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_424
  have b26_425 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K26.b8 (by decide) (by decide)).trans b25_425
  have b26_426 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K26.b8 (by decide) (by decide)).trans b25_426
  have b26_427 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K26.b8 (by decide) (by decide)).trans b25_427
  have w26_318 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by
    rw [← w25_428]
    exact ld_cp fun q hq => by
      have := X26 (0x3 + q) (by omega)
      rwa [show 0x315 + (0x3 + q) = 0x318 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w26_31c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = BitVec.ofNat 32 tl21.len := by
    rw [← w25_42c]
    exact ld_cp fun q hq => by
      have := X26 (0x7 + q) (by omega)
      rwa [show 0x315 + (0x7 + q) = 0x31C + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b26_315 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x315) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [show 0x315 = 0x315 + 0x0 from rfl, X26 0x0 (by decide)]; exact b25_425
  have b26_316 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x316) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [show 0x316 = 0x315 + 0x1 from rfl, X26 0x1 (by decide)]; exact b25_426
  have b26_317 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x317) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [show 0x317 = 0x315 + 0x2 from rfl, X26 0x2 (by decide)]; exact b25_427
  clear b25_424 w25_42c w25_428 w25_424 w25_420 w25_30c w25_308 w25_304 w25_300 w25_2ec w25_2e8 g25_12 g25_11 g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0xBA2: lw
  obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_ba2 (off' := 0xBA6) (by decide)
    (by rw [g26_2, show B + 0x21A0 + 0x30C = B + 0x21A0 + BitVec.ofNat 32 0x30C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s27 : St n27.mem SV n27 0xBA6 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
  have g27_10 : reg n27 a0 = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by
    rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g26_2, show B + 0x21A0 + 0x30C = B + 0x21A0 + BitVec.ofNat 32 0x30C by sv_addr, w26_30c]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_2e8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_2e8
  have w27_2ec : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_2ec
  have w27_300 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m27]; exact w26_300
  have w27_304 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m27]; exact w26_304
  have w27_308 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m27]; exact w26_308
  have w27_30c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m27]; exact w26_30c
  have w27_318 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m27]; exact w26_318
  have w27_31c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = BitVec.ofNat 32 tl21.len := by rw [m27]; exact w26_31c
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m27]; exact w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m27]; exact w26_424
  have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m27]; exact w26_428
  have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m27]; exact w26_42c
  have b27_315 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x315) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m27]; exact b26_315
  have b27_316 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x316) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m27]; exact b26_316
  have b27_317 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x317) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m27]; exact b26_317
  have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m27]; exact b26_424
  have b27_425 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m27]; exact b26_425
  have b27_426 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m27]; exact b26_426
  have b27_427 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m27]; exact b26_427
  clear b26_317 b26_316 b26_315 w26_31c w26_318 b26_427 b26_426 b26_425 b26_424 w26_42c w26_428 w26_424 w26_420 w26_30c w26_308 w26_304 w26_300 w26_2ec w26_2e8 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 s26 X26 K26 P26 b25_427 b25_426 b25_425
  -- 0xBA6: sw
  obtain ⟨n28, d28, s28, fr28, K28, W28, rg28⟩ := sv_sw F E27 s27 sv_at_ba6 (off' := 0xBAA) (c := 0x310)
    (by decide) (by rw [g27_2]; sv_addr) (by decide) (by decide)
  have t28 : Steps n0 n28 := t27.trans d28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keep K28 (by decide)
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rg28 sp, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg28 (3 : Fin 32), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg28 (4 : Fin 32), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg28 (8 : Fin 32), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [rg28 (9 : Fin 32), g27_9]
  have g28_10 : reg n28 a0 = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [rg28 a0, g27_10]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rg28 (18 : Fin 32), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rg28 (19 : Fin 32), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [rg28 (20 : Fin 32), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [rg28 (21 : Fin 32), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [rg28 (22 : Fin 32), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [rg28 (23 : Fin 32), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [rg28 (24 : Fin 32), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [rg28 (25 : Fin 32), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [rg28 (26 : Fin 32), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [rg28 (27 : Fin 32), g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4)] := keep_kk27.trans K28.toL
  clear keep_kk27
  have w28_2e8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K28.w32 (by decide) (by decide)).trans w27_2e8
  have w28_2ec : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K28.w32 (by decide) (by decide)).trans w27_2ec
  have w28_300 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K28.w32 (by decide) (by decide)).trans w27_300
  have w28_304 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K28.w32 (by decide) (by decide)).trans w27_304
  have w28_308 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K28.w32 (by decide) (by decide)).trans w27_308
  have w28_30c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K28.w32 (by decide) (by decide)).trans w27_30c
  have w28_318 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K28.w32 (by decide) (by decide)).trans w27_318
  have w28_31c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = BitVec.ofNat 32 tl21.len := (K28.w32 (by decide) (by decide)).trans w27_31c
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K28.w32 (by decide) (by decide)).trans w27_420
  have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := (K28.w32 (by decide) (by decide)).trans w27_424
  have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K28.w32 (by decide) (by decide)).trans w27_428
  have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := (K28.w32 (by decide) (by decide)).trans w27_42c
  have b28_315 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x315) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K28.b8 (by decide) (by decide)).trans b27_315
  have b28_316 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x316) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K28.b8 (by decide) (by decide)).trans b27_316
  have b28_317 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x317) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K28.b8 (by decide) (by decide)).trans b27_317
  have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_424
  have b28_425 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K28.b8 (by decide) (by decide)).trans b27_425
  have b28_426 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K28.b8 (by decide) (by decide)).trans b27_426
  have b28_427 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K28.b8 (by decide) (by decide)).trans b27_427
  have w28_310 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [W28, g27_9]
  clear b27_427 b27_426 b27_425 b27_424 b27_317 b27_316 b27_315 w27_42c w27_428 w27_424 w27_420 w27_31c w27_318 w27_30c w27_308 w27_304 w27_300 w27_2ec w27_2e8 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  -- 0xBAA: sb
  obtain ⟨n29, d29, s29, fr29, K29, W29, rg29⟩ := sv_sb F E28 s28 sv_at_baa (off' := 0xBAE) (c := 0x314)
    (by decide) (by rw [g28_2]; sv_addr) (by decide)
  have t29 : Steps n0 n29 := t28.trans d29
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.keep K29 (by decide)
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [rg29 sp, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg29 (3 : Fin 32), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg29 (4 : Fin 32), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg29 (8 : Fin 32), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [rg29 (9 : Fin 32), g28_9]
  have g29_10 : reg n29 a0 = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [rg29 a0, g28_10]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [rg29 (18 : Fin 32), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [rg29 (19 : Fin 32), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [rg29 (20 : Fin 32), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [rg29 (21 : Fin 32), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [rg29 (22 : Fin 32), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [rg29 (23 : Fin 32), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [rg29 (24 : Fin 32), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [rg29 (25 : Fin 32), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [rg29 (26 : Fin 32), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = x27 := by rw [rg29 (27 : Fin 32), g28_27]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1)] := keep_kk28.trans K29.toL
  clear keep_kk28
  have w29_2e8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K29.w32 (by decide) (by decide)).trans w28_2e8
  have w29_2ec : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K29.w32 (by decide) (by decide)).trans w28_2ec
  have w29_300 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K29.w32 (by decide) (by decide)).trans w28_300
  have w29_304 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K29.w32 (by decide) (by decide)).trans w28_304
  have w29_308 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K29.w32 (by decide) (by decide)).trans w28_308
  have w29_30c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K29.w32 (by decide) (by decide)).trans w28_30c
  have w29_310 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K29.w32 (by decide) (by decide)).trans w28_310
  have w29_318 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K29.w32 (by decide) (by decide)).trans w28_318
  have w29_31c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = BitVec.ofNat 32 tl21.len := (K29.w32 (by decide) (by decide)).trans w28_31c
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K29.w32 (by decide) (by decide)).trans w28_420
  have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := (K29.w32 (by decide) (by decide)).trans w28_424
  have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K29.w32 (by decide) (by decide)).trans w28_428
  have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := (K29.w32 (by decide) (by decide)).trans w28_42c
  have b29_315 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x315) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K29.b8 (by decide) (by decide)).trans b28_315
  have b29_316 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x316) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K29.b8 (by decide) (by decide)).trans b28_316
  have b29_317 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x317) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K29.b8 (by decide) (by decide)).trans b28_317
  have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := (K29.b8 (by decide) (by decide)).trans b28_424
  have b29_425 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := (K29.b8 (by decide) (by decide)).trans b28_425
  have b29_426 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := (K29.b8 (by decide) (by decide)).trans b28_426
  have b29_427 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := (K29.b8 (by decide) (by decide)).trans b28_427
  have b29_314 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [W29, g28_8, lbu_low]
  clear w28_310 b28_427 b28_426 b28_425 b28_424 b28_317 b28_316 b28_315 w28_42c w28_428 w28_424 w28_420 w28_31c w28_318 w28_30c w28_308 w28_304 w28_300 w28_2ec w28_2e8 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 rg28 W28 K28 fr28 s28 d28
  have w29_314 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := ld_of_bytes b29_314
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x314 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x315 by sv_addr]; exact b29_315)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x314 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x316 by sv_addr]; exact b29_316)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x314 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x317 by sv_addr]; exact b29_317)
  by_cases hcrem : ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) = 0
  rotate_left
  · -- 0xBAE: branch, taken
    obtain ⟨n30, d30, u30⟩ := s29.taken E29.self 0x14C sv_at_bae
      (by decide) (by rw [g29_10, s29.zero]; exact br_bne_t hcrem)
    have s30 : St n30.mem SV n30 0x14C (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [u30.regs, g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [u30.regs, g29_9]
    have g30_10 : reg n30 a0 = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [u30.regs, g29_10]
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
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_2e8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m30]; exact w29_2e8
    have w30_2ec : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m30]; exact w29_2ec
    have w30_300 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m30]; exact w29_300
    have w30_304 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m30]; exact w29_304
    have w30_308 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m30]; exact w29_308
    have w30_30c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m30]; exact w29_30c
    have w30_310 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m30]; exact w29_310
    have w30_314 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m30]; exact w29_314
    have w30_318 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m30]; exact w29_318
    have w30_31c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = BitVec.ofNat 32 tl21.len := by rw [m30]; exact w29_31c
    have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m30]; exact w29_420
    have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m30]; exact w29_424
    have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m30]; exact w29_428
    have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m30]; exact w29_42c
    have b30_424 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m30]; exact b29_424
    have b30_425 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m30]; exact b29_425
    have b30_426 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m30]; exact b29_426
    have b30_427 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m30]; exact b29_427
    clear b29_314 b29_427 b29_426 b29_425 b29_424 b29_317 b29_316 b29_315 w29_42c w29_428 w29_424 w29_420 w29_31c w29_318 w29_310 w29_30c w29_308 w29_304 w29_300 w29_2ec w29_2e8 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 rg29 W29 K29 fr29 s29 d29
    -- 0x14C
    obtain ⟨n31, c31, u31⟩ := s30.block svTr214c E30.self svTr214c_end
      ⟨trivial, trivial⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have s31 : St n31.mem SV n31 0x14E (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have rb31 : ∀ q, reg n31 q = (runBlock svTr214c (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans c31
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by
      rw [rb31, runBlock_reg _ _ _ sp s30.zero (by decide), g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb31, runBlock_reg _ _ _ (3 : Fin 32) s30.zero (by decide), g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb31, runBlock_reg _ _ _ (4 : Fin 32) s30.zero (by decide), g30_4]
    have g31_9 : reg n31 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by
      rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
    have g31_10 : reg n31 a0 = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by
      rw [rb31, runBlock_reg _ _ _ a0 s30.zero (by decide), g30_10]
    have g31_18 : reg n31 (18 : Fin 32) = out := by
      rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by
      rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = x20 := by
      rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = x21 := by
      rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = x22 := by
      rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = x23 := by
      rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = x24 := by
      rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = x25 := by
      rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = x26 := by
      rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = x27 := by
      rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
    have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb31]; simp +decide only [runBlock, BInstr.run, svTr214c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_2e8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m31]; exact w30_2e8
    have w31_2ec : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m31]; exact w30_2ec
    have w31_300 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m31]; exact w30_300
    have w31_304 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m31]; exact w30_304
    have w31_308 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m31]; exact w30_308
    have w31_30c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m31]; exact w30_30c
    have w31_310 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_310
    have w31_314 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_314
    have w31_318 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_318
    have w31_31c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_31c
    have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_420
    have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_424
    have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_428
    have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_42c
    have b31_424 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m31]; exact b30_424
    have b31_425 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m31]; exact b30_425
    have b31_426 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m31]; exact b30_426
    have b31_427 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m31]; exact b30_427
    clear b30_427 b30_426 b30_425 b30_424 w30_42c w30_428 w30_424 w30_420 w30_31c w30_318 w30_314 w30_310 w30_30c w30_308 w30_304 w30_300 w30_2ec w30_2e8 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
    -- 0x14E: j
    obtain ⟨n32, d32, u32⟩ := s31.jump E31.self sv_at_14e (off' := 0x7A4) (by decide)
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
    have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [u32.regs, g31_10]
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
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_2e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m32]; exact w31_2e8
    have w32_2ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m32]; exact w31_2ec
    have w32_300 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m32]; exact w31_300
    have w32_304 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m32]; exact w31_304
    have w32_308 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m32]; exact w31_308
    have w32_30c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m32]; exact w31_30c
    have w32_310 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_310
    have w32_314 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_314
    have w32_318 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_318
    have w32_31c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_31c
    have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_420
    have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_424
    have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m32]; exact w31_428
    have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m32]; exact w31_42c
    have b32_424 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m32]; exact b31_424
    have b32_425 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m32]; exact b31_425
    have b32_426 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m32]; exact b31_426
    have b32_427 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m32]; exact b31_427
    clear b31_427 b31_426 b31_425 b31_424 w31_42c w31_428 w31_424 w31_420 w31_31c w31_318 w31_314 w31_310 w31_30c w31_308 w31_304 w31_300 w31_2ec w31_2e8 g31_8 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
    exact .inl ⟨(fun ⟨tl2', h0', h1', op13', ol13', h2', to13', h3', h4', tl21', h5', h6', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [ht13] at h3'; cases h3'; rw [hr21] at h5'; cases h5'; exact hcrem h6'), sv_fail F E32 s32 t32 (fun x hx => (fR32 x hx).trans (fM x hx).symm) V32 hret g32_2 g32_18 hO g32_3 g32_4 (by rw [g32_8]; sv_code)⟩
  -- 0xBAE: branch, not taken
  obtain ⟨n30, d30, u30⟩ := s29.notTaken E29.self 0xBB2 sv_at_bae
    (by decide) (by rw [g29_10, s29.zero]; exact br_bne_f hcrem)
  have s30 : St n30.mem SV n30 0xBB2 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [u30.regs, g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [u30.regs, g29_9]
  have g30_10 : reg n30 a0 = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [u30.regs, g29_10]
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
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_2e8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m30]; exact w29_2e8
  have w30_2ec : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m30]; exact w29_2ec
  have w30_300 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m30]; exact w29_300
  have w30_304 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m30]; exact w29_304
  have w30_308 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m30]; exact w29_308
  have w30_30c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m30]; exact w29_30c
  have w30_310 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m30]; exact w29_310
  have w30_314 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m30]; exact w29_314
  have w30_318 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m30]; exact w29_318
  have w30_31c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = BitVec.ofNat 32 tl21.len := by rw [m30]; exact w29_31c
  have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m30]; exact w29_420
  have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m30]; exact w29_424
  have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m30]; exact w29_428
  have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m30]; exact w29_42c
  have b30_424 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m30]; exact b29_424
  have b30_425 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m30]; exact b29_425
  have b30_426 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m30]; exact b29_426
  have b30_427 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m30]; exact b29_427
  clear b29_314 b29_427 b29_426 b29_425 b29_424 b29_317 b29_316 b29_315 w29_42c w29_428 w29_424 w29_420 w29_31c w29_318 w29_310 w29_30c w29_308 w29_304 w29_300 w29_2ec w29_2e8 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 rg29 W29 K29 fr29 s29 d29
  -- 0xBB2
  obtain ⟨n31, c31, u31⟩ := s30.block svTr2bb2 E30.self svTr2bb2_end
    ⟨trivial, trivial, trivial⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have s31 : St n31.mem SV n31 0xBB8 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have rb31 : ∀ q, reg n31 q = (runBlock svTr2bb2 (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans c31
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by
    rw [rb31, runBlock_reg _ _ _ sp s30.zero (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (3 : Fin 32) s30.zero (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (4 : Fin 32) s30.zero (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb31, runBlock_reg _ _ _ (8 : Fin 32) s30.zero (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by
    rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
  have g31_18 : reg n31 (18 : Fin 32) = out := by
    rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by
    rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = x20 := by
    rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by
    rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by
    rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = x23 := by
    rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = x24 := by
    rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = x25 := by
    rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by
    rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = x27 := by
    rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
  have g31_10 : reg n31 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svTr2bb2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g31_11 : reg n31 a1 = B + 0x21A0 + BitVec.ofNat 32 0x310 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svTr2bb2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_2e8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m31]; exact w30_2e8
  have w31_2ec : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m31]; exact w30_2ec
  have w31_300 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m31]; exact w30_300
  have w31_304 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m31]; exact w30_304
  have w31_308 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m31]; exact w30_308
  have w31_30c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m31]; exact w30_30c
  have w31_310 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_310
  have w31_314 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_314
  have w31_318 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_318
  have w31_31c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_31c
  have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_420
  have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_424
  have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m31]; exact w30_428
  have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl21.len := by rw [m31]; exact w30_42c
  have b31_424 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl21.len).extractLsb' 0 8 := by rw [m31]; exact b30_424
  have b31_425 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl21.len).extractLsb' 8 8 := by rw [m31]; exact b30_425
  have b31_426 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl21.len).extractLsb' 16 8 := by rw [m31]; exact b30_426
  have b31_427 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl21.len).extractLsb' 24 8 := by rw [m31]; exact b30_427
  clear b30_427 b30_426 b30_425 b30_424 w30_42c w30_428 w30_424 w30_420 w30_31c w30_318 w30_314 w30_310 w30_30c w30_308 w30_304 w30_300 w30_2ec w30_2e8 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30 w29_314
  -- 0xBB8: sv_seqF
  obtain ⟨n32, c32, s32, sp32, rk32, K32, Ok32, Er32, fr32⟩ := sv_seqF (oc := 0x420) (dc := 0x310)
    F E31 s31 sv_at_bb8 sv_at_bbc (by decide) (by decide) g31_2 g31_10 g31_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w31_318 w31_31c (((r_in.contentW hr2).restW (derOid_ok_elem ht13)).contentW hr21)
  have t32 : Steps n0 n32 := t31.trans c32
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.keepL K32 (by decide)
  rw [sv_mb fR31 (((r_in.contentW hr2).restW (derOid_ok_elem ht13)).contentW hr21)] at Ok32 Er32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [rk32 sp (by decide) (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk32 (3 : Fin 32) (by decide) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk32 (4 : Fin 32) (by decide) (by decide), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk32 (8 : Fin 32) (by decide) (by decide), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [rk32 (9 : Fin 32) (by decide) (by decide), g31_9]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [rk32 (18 : Fin 32) (by decide) (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [rk32 (19 : Fin 32) (by decide) (by decide), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [rk32 (20 : Fin 32) (by decide) (by decide), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [rk32 (21 : Fin 32) (by decide) (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [rk32 (22 : Fin 32) (by decide) (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [rk32 (23 : Fin 32) (by decide) (by decide), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = x24 := by rw [rk32 (24 : Fin 32) (by decide) (by decide), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = x25 := by rw [rk32 (25 : Fin 32) (by decide) (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [rk32 (26 : Fin 32) (by decide) (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = x27 := by rw [rk32 (27 : Fin 32) (by decide) (by decide), g31_27]
  obtain ⟨r32, hr32⟩ : ∃ r, derElement 0x30 (memBytes M0 ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) (BitVec.ofNat 32 tl21.len).toNat) = r := ⟨_, rfl⟩
  rcases r32 with er32 | tl32
  · obtain ⟨z32, ez32⟩ := Er32 er32 hr32
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8)] := keep_kk31.trans K32
    clear keep_kk31
    have w32_2e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K32.w32 (by decide) (by decide)).trans w31_2e8
    have w32_2ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K32.w32 (by decide) (by decide)).trans w31_2ec
    have w32_300 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K32.w32 (by decide) (by decide)).trans w31_300
    have w32_304 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K32.w32 (by decide) (by decide)).trans w31_304
    have w32_308 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K32.w32 (by decide) (by decide)).trans w31_308
    have w32_30c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K32.w32 (by decide) (by decide)).trans w31_30c
    have w32_310 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K32.w32 (by decide) (by decide)).trans w31_310
    have w32_314 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := (K32.w32 (by decide) (by decide)).trans w31_314
    have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z32
    have b32_424 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er32 := ez32
    clear b31_427 b31_426 b31_425 b31_424 w31_42c w31_428 w31_424 w31_420 w31_31c w31_318 w31_314 w31_310 w31_30c w31_308 w31_304 w31_300 w31_2ec w31_2e8 g31_11 g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
    -- 0xBC0: lw
    obtain ⟨n33, d33, u33⟩ := s32.lw E32.self sv_at_bc0 (off' := 0xBC4) (by decide)
      (by rw [g32_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s33 : St n33.mem SV n33 0xBC4 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
    have m33 : n33.mem = n32.mem := u33.mem
    have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
    have t33 : Steps n0 n33 := t32.trans (.single d33)
    have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
    have E33 : SvCode n33.mem := E32.fr F fr33
    have V33 : SvSaves B n33.mem v := V32.same m33
    have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_2]
    have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, upd_ne (by decide) (by decide), g32_3]
    have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, upd_ne (by decide) (by decide), g32_4]
    have g33_8 : reg n33 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_8]
    have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, upd_ne (by decide) (by decide), g32_18]
    have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, upd_ne (by decide) (by decide), g32_19]
    have g33_20 : reg n33 (20 : Fin 32) = x20 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_20]
    have g33_21 : reg n33 (21 : Fin 32) = x21 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_21]
    have g33_22 : reg n33 (22 : Fin 32) = x22 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_22]
    have g33_23 : reg n33 (23 : Fin 32) = x23 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = x24 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = x25 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = x27 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_27]
    have g33_9 : reg n33 (9 : Fin 32) = 0 := by
      rw [u33.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g32_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w32_420]
    have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8)] := by rw [m33]; exact keep_kk32
    clear keep_kk32
    have w33_2e8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m33]; exact w32_2e8
    have w33_2ec : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m33]; exact w32_2ec
    have w33_300 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m33]; exact w32_300
    have w33_304 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m33]; exact w32_304
    have w33_308 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m33]; exact w32_308
    have w33_30c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m33]; exact w32_30c
    have w33_310 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m33]; exact w32_310
    have w33_314 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m33]; exact w32_314
    have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m33]; exact w32_420
    have b33_424 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er32 := by rw [m33]; exact b32_424
    clear b32_424 w32_420 w32_314 w32_310 w32_30c w32_308 w32_304 w32_300 w32_2ec w32_2e8 ez32 z32
    -- 0xBC4: lbu
    obtain ⟨n34, d34, u34⟩ := s33.lbu E33.self sv_at_bc4 (off' := 0xBC8) (by decide)
    have s34 : St n34.mem SV n34 0xBC8 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
    have m34 : n34.mem = n33.mem := u34.mem
    have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
    have t34 : Steps n0 n34 := t33.trans (.single d34)
    have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.same m34
    have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
    have g34_9 : reg n34 (9 : Fin 32) = 0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_9]
    have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, upd_ne (by decide) (by decide), g33_18]
    have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_19]
    have g34_20 : reg n34 (20 : Fin 32) = x20 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_20]
    have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_21]
    have g34_22 : reg n34 (22 : Fin 32) = x22 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_22]
    have g34_23 : reg n34 (23 : Fin 32) = x23 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_23]
    have g34_24 : reg n34 (24 : Fin 32) = x24 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_24]
    have g34_25 : reg n34 (25 : Fin 32) = x25 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_25]
    have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_26]
    have g34_27 : reg n34 (27 : Fin 32) = x27 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_27]
    have g34_8 : reg n34 (8 : Fin 32) = (derErrByte er32).zeroExtend 32 := by
      rw [u34.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g33_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b33_424]
    have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8)] := by rw [m34]; exact keep_kk33
    clear keep_kk33
    have w34_2e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m34]; exact w33_2e8
    have w34_2ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m34]; exact w33_2ec
    have w34_300 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m34]; exact w33_300
    have w34_304 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m34]; exact w33_304
    have w34_308 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m34]; exact w33_308
    have w34_30c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m34]; exact w33_30c
    have w34_310 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m34]; exact w33_310
    have w34_314 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m34]; exact w33_314
    have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m34]; exact w33_420
    have b34_424 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er32 := by rw [m34]; exact b33_424
    clear b33_424 w33_420 w33_314 w33_310 w33_30c w33_308 w33_304 w33_300 w33_2ec w33_2e8 g33_9 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
    -- 0xBC8: branch, taken
    obtain ⟨n35, d35, u35⟩ := s34.taken E34.self 0x7A4 sv_at_bc8
      (by decide) (by rw [g34_9, s34.zero]; rfl)
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
    have g35_8 : reg n35 (8 : Fin 32) = (derErrByte er32).zeroExtend 32 := by rw [u35.regs, g34_8]
    have g35_9 : reg n35 (9 : Fin 32) = 0 := by rw [u35.regs, g34_9]
    have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
    have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
    have g35_20 : reg n35 (20 : Fin 32) = x20 := by rw [u35.regs, g34_20]
    have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [u35.regs, g34_21]
    have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [u35.regs, g34_22]
    have g35_23 : reg n35 (23 : Fin 32) = x23 := by rw [u35.regs, g34_23]
    have g35_24 : reg n35 (24 : Fin 32) = x24 := by rw [u35.regs, g34_24]
    have g35_25 : reg n35 (25 : Fin 32) = x25 := by rw [u35.regs, g34_25]
    have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [u35.regs, g34_26]
    have g35_27 : reg n35 (27 : Fin 32) = x27 := by rw [u35.regs, g34_27]
    have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8)] := by rw [m35]; exact keep_kk34
    clear keep_kk34
    have w35_2e8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m35]; exact w34_2e8
    have w35_2ec : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m35]; exact w34_2ec
    have w35_300 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m35]; exact w34_300
    have w35_304 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m35]; exact w34_304
    have w35_308 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m35]; exact w34_308
    have w35_30c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m35]; exact w34_30c
    have w35_310 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m35]; exact w34_310
    have w35_314 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m35]; exact w34_314
    have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m35]; exact w34_420
    have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er32 := by rw [m35]; exact b34_424
    clear b34_424 w34_420 w34_314 w34_310 w34_30c w34_308 w34_304 w34_300 w34_2ec w34_2e8 g34_8 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
    exact .inl ⟨(fun ⟨tl2', h0', h1', op13', ol13', h2', to13', h3', h4', tl21', h5', h6', tl32', h7', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [ht13] at h3'; cases h3'; rw [hr21] at h5'; cases h5'; rw [hr32] at h7'; cases h7'), sv_fail F E35 s35 t35 (fun x hx => (fR35 x hx).trans (fM x hx).symm) V35 hret g35_2 g35_18 hO g35_3 g35_4 (by rw [g35_8]; sv_code)⟩
  obtain ⟨o0_32, o4_32, o8_32, o12_32, d8_32, d12_32⟩ := Ok32 tl32 hr32
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8)] := keep_kk31.trans K32
  clear keep_kk31
  have w32_2e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K32.w32 (by decide) (by decide)).trans w31_2e8
  have w32_2ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K32.w32 (by decide) (by decide)).trans w31_2ec
  have w32_300 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K32.w32 (by decide) (by decide)).trans w31_300
  have w32_304 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K32.w32 (by decide) (by decide)).trans w31_304
  have w32_308 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K32.w32 (by decide) (by decide)).trans w31_308
  have w32_30c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K32.w32 (by decide) (by decide)).trans w31_30c
  have w32_310 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K32.w32 (by decide) (by decide)).trans w31_310
  have w32_314 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := (K32.w32 (by decide) (by decide)).trans w31_314
  have w32_318 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := d8_32
  have w32_31c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := d12_32
  have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := o0_32
  have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := o4_32
  have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := o8_32
  have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := o12_32
  clear b31_427 b31_426 b31_425 b31_424 w31_42c w31_428 w31_424 w31_420 w31_31c w31_318 w31_314 w31_310 w31_30c w31_308 w31_304 w31_300 w31_2ec w31_2e8 g31_11 g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
  -- 0xBC0: lw
  obtain ⟨n33, d33, u33⟩ := s32.lw E32.self sv_at_bc0 (off' := 0xBC4) (by decide)
    (by rw [g32_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s33 : St n33.mem SV n33 0xBC4 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans (.single d33)
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, upd_ne (by decide) (by decide), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, upd_ne (by decide) (by decide), g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = ((BitVec.ofNat 32 tl21.len).extractLsb' 0 8).zeroExtend 32 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_8]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, upd_ne (by decide) (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, upd_ne (by decide) (by decide), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = x20 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = x21 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = x22 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = x23 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = x24 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = x25 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = x27 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_27]
  have g33_9 : reg n33 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by
    rw [u33.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g32_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w32_420]
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_2e8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m33]; exact w32_2e8
  have w33_2ec : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m33]; exact w32_2ec
  have w33_300 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m33]; exact w32_300
  have w33_304 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m33]; exact w32_304
  have w33_308 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m33]; exact w32_308
  have w33_30c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m33]; exact w32_30c
  have w33_310 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m33]; exact w32_310
  have w33_314 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m33]; exact w32_314
  have w33_318 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m33]; exact w32_318
  have w33_31c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m33]; exact w32_31c
  have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m33]; exact w32_420
  have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m33]; exact w32_424
  have w33_428 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m33]; exact w32_428
  have w33_42c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m33]; exact w32_42c
  clear w32_42c w32_428 w32_424 w32_420 w32_31c w32_318 w32_314 w32_310 w32_30c w32_308 w32_304 w32_300 w32_2ec w32_2e8 d12_32 d8_32 o12_32 o8_32 o4_32 o0_32 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 Er32 Ok32 K32 rk32 sp32 s32 c32
  -- 0xBC4: lbu
  obtain ⟨n34, d34, u34⟩ := s33.lbu E33.self sv_at_bc4 (off' := 0xBC8) (by decide)
  have b33_424 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by
    have h := byte_of_ld w33_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s34 : St n34.mem SV n34 0xBC8 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans (.single d34)
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
  have g34_9 : reg n34 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u34.regs, upd_ne (by decide) (by decide), g33_9]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, upd_ne (by decide) (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = x20 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = x22 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = x23 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = x24 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = x25 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = x27 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_27]
  have g34_8 : reg n34 (8 : Fin 32) = ((BitVec.ofNat 32 tl32.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u34.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g33_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b33_424]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_2e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m34]; exact w33_2e8
  have w34_2ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m34]; exact w33_2ec
  have w34_300 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m34]; exact w33_300
  have w34_304 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m34]; exact w33_304
  have w34_308 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m34]; exact w33_308
  have w34_30c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m34]; exact w33_30c
  have w34_310 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m34]; exact w33_310
  have w34_314 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m34]; exact w33_314
  have w34_318 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m34]; exact w33_318
  have w34_31c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m34]; exact w33_31c
  have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m34]; exact w33_420
  have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m34]; exact w33_424
  have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m34]; exact w33_428
  have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m34]; exact w33_42c
  have b34_424 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m34]; exact b33_424
  clear w33_42c w33_428 w33_424 w33_420 w33_31c w33_318 w33_314 w33_310 w33_30c w33_308 w33_304 w33_300 w33_2ec w33_2e8 g33_9 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
  -- 0xBC8: branch, not taken
  obtain ⟨n35, d35, u35⟩ := s34.notTaken E34.self 0xBCC sv_at_bc8
    (by decide) (by rw [g34_9, s34.zero]; exact br_beq_f ((((r_in.contentW hr2).restW (derOid_ok_elem ht13)).contentW hr21).ok_ne hr32))
  have s35 : St n35.mem SV n35 0xBCC (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans (.single d35)
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = ((BitVec.ofNat 32 tl32.len).extractLsb' 0 8).zeroExtend 32 := by rw [u35.regs, g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u35.regs, g34_9]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = x20 := by rw [u35.regs, g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [u35.regs, g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [u35.regs, g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = x23 := by rw [u35.regs, g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = x24 := by rw [u35.regs, g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = x25 := by rw [u35.regs, g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [u35.regs, g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = x27 := by rw [u35.regs, g34_27]
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_2e8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m35]; exact w34_2e8
  have w35_2ec : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m35]; exact w34_2ec
  have w35_300 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m35]; exact w34_300
  have w35_304 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m35]; exact w34_304
  have w35_308 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m35]; exact w34_308
  have w35_30c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m35]; exact w34_30c
  have w35_310 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m35]; exact w34_310
  have w35_314 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m35]; exact w34_314
  have w35_318 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m35]; exact w34_318
  have w35_31c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m35]; exact w34_31c
  have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m35]; exact w34_420
  have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m35]; exact w34_424
  have w35_428 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m35]; exact w34_428
  have w35_42c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m35]; exact w34_42c
  have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m35]; exact b34_424
  clear b34_424 w34_42c w34_428 w34_424 w34_420 w34_31c w34_318 w34_314 w34_310 w34_30c w34_308 w34_304 w34_300 w34_2ec w34_2e8 g34_8 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 b33_424 u34 d34
  -- 0xBCC
  obtain ⟨n36, c36, u36⟩ := s35.block svTr2bcc E35.self svTr2bcc_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have s36 : St n36.mem SV n36 0xBD6 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have rb36 : ∀ q, reg n36 q = (runBlock svTr2bcc (n35.mem, reg n35)).2 q := fun q => by rw [u36.regs]
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
  have g36_8 : reg n36 (8 : Fin 32) = ((BitVec.ofNat 32 tl32.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb36, runBlock_reg _ _ _ (8 : Fin 32) s35.zero (by decide), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by
    rw [rb36, runBlock_reg _ _ _ (9 : Fin 32) s35.zero (by decide), g35_9]
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
  have g36_24 : reg n36 (24 : Fin 32) = x24 := by
    rw [rb36, runBlock_reg _ _ _ (24 : Fin 32) s35.zero (by decide), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = x25 := by
    rw [rb36, runBlock_reg _ _ _ (25 : Fin 32) s35.zero (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by
    rw [rb36, runBlock_reg _ _ _ (26 : Fin 32) s35.zero (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = x27 := by
    rw [rb36, runBlock_reg _ _ _ (27 : Fin 32) s35.zero (by decide), g35_27]
  have g36_10 : reg n36 a0 = B + 0x21A0 + BitVec.ofNat 32 0x325 := by
    rw [rb36]; simp +decide only [runBlock, BInstr.run, svTr2bcc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, s35.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g36_11 : reg n36 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb36]; simp +decide only [runBlock, BInstr.run, svTr2bcc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, s35.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g36_12 : reg n36 a2 = BitVec.ofNat 32 0xB := by
    rw [rb36]; simp +decide only [runBlock, BInstr.run, svTr2bcc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, s35.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_2e8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m36]; exact w35_2e8
  have w36_2ec : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m36]; exact w35_2ec
  have w36_300 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m36]; exact w35_300
  have w36_304 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m36]; exact w35_304
  have w36_308 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m36]; exact w35_308
  have w36_30c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m36]; exact w35_30c
  have w36_310 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m36]; exact w35_310
  have w36_314 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m36]; exact w35_314
  have w36_318 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m36]; exact w35_318
  have w36_31c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m36]; exact w35_31c
  have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m36]; exact w35_420
  have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m36]; exact w35_424
  have w36_428 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m36]; exact w35_428
  have w36_42c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m36]; exact w35_42c
  have b36_424 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m36]; exact b35_424
  clear b35_424 w35_42c w35_428 w35_424 w35_420 w35_31c w35_318 w35_314 w35_310 w35_30c w35_308 w35_304 w35_300 w35_2ec w35_2e8 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
  have b36_425 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by
    have h := byte_of_ld w36_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b36_426 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by
    have h := byte_of_ld w36_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b36_427 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by
    have h := byte_of_ld w36_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0xBD6: memcpy
  obtain ⟨n37, P37, K37, X37⟩ := sv_mc (c := 0x325) (d := 0x425) (N := 0xB) F E36 s36 sv_at_bd6 sv_at_bda
    (by decide) (by decide) g36_2 g36_10 g36_11 g36_12
    (by decide) (by decide) (by decide)
  have s37 := P37.st
  have fr37 := P37.fr
  have t37 : Steps n0 n37 := t36.trans P37.steps
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.keep K37 (by decide)
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [P37.regs sp (by decide), g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P37.regs (3 : Fin 32) (by decide), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P37.regs (4 : Fin 32) (by decide), g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = ((BitVec.ofNat 32 tl32.len).extractLsb' 0 8).zeroExtend 32 := by rw [P37.regs (8 : Fin 32) (by decide), g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [P37.regs (9 : Fin 32) (by decide), g36_9]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [P37.regs (18 : Fin 32) (by decide), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [P37.regs (19 : Fin 32) (by decide), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = x20 := by rw [P37.regs (20 : Fin 32) (by decide), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [P37.regs (21 : Fin 32) (by decide), g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = x22 := by rw [P37.regs (22 : Fin 32) (by decide), g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = x23 := by rw [P37.regs (23 : Fin 32) (by decide), g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = x24 := by rw [P37.regs (24 : Fin 32) (by decide), g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = x25 := by rw [P37.regs (25 : Fin 32) (by decide), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [P37.regs (26 : Fin 32) (by decide), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = x27 := by rw [P37.regs (27 : Fin 32) (by decide), g36_27]
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB)] := keep_kk36.trans K37.toL
  clear keep_kk36
  have w37_2e8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K37.w32 (by decide) (by decide)).trans w36_2e8
  have w37_2ec : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K37.w32 (by decide) (by decide)).trans w36_2ec
  have w37_300 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K37.w32 (by decide) (by decide)).trans w36_300
  have w37_304 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K37.w32 (by decide) (by decide)).trans w36_304
  have w37_308 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K37.w32 (by decide) (by decide)).trans w36_308
  have w37_30c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K37.w32 (by decide) (by decide)).trans w36_30c
  have w37_310 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K37.w32 (by decide) (by decide)).trans w36_310
  have w37_314 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := (K37.w32 (by decide) (by decide)).trans w36_314
  have w37_318 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := (K37.w32 (by decide) (by decide)).trans w36_318
  have w37_31c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := (K37.w32 (by decide) (by decide)).trans w36_31c
  have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K37.w32 (by decide) (by decide)).trans w36_420
  have w37_424 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := (K37.w32 (by decide) (by decide)).trans w36_424
  have w37_428 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K37.w32 (by decide) (by decide)).trans w36_428
  have w37_42c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := (K37.w32 (by decide) (by decide)).trans w36_42c
  have b37_424 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := (K37.b8 (by decide) (by decide)).trans b36_424
  have b37_425 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := (K37.b8 (by decide) (by decide)).trans b36_425
  have b37_426 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := (K37.b8 (by decide) (by decide)).trans b36_426
  have b37_427 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := (K37.b8 (by decide) (by decide)).trans b36_427
  have w37_328 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by
    rw [← w36_428]
    exact ld_cp fun q hq => by
      have := X37 (0x3 + q) (by omega)
      rwa [show 0x325 + (0x3 + q) = 0x328 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w37_32c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = BitVec.ofNat 32 tl32.len := by
    rw [← w36_42c]
    exact ld_cp fun q hq => by
      have := X37 (0x7 + q) (by omega)
      rwa [show 0x325 + (0x7 + q) = 0x32C + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b37_325 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x325) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [show 0x325 = 0x325 + 0x0 from rfl, X37 0x0 (by decide)]; exact b36_425
  have b37_326 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x326) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [show 0x326 = 0x325 + 0x1 from rfl, X37 0x1 (by decide)]; exact b36_426
  have b37_327 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x327) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [show 0x327 = 0x325 + 0x2 from rfl, X37 0x2 (by decide)]; exact b36_427
  clear b36_424 w36_42c w36_428 w36_424 w36_420 w36_31c w36_318 w36_314 w36_310 w36_30c w36_308 w36_304 w36_300 w36_2ec w36_2e8 g36_12 g36_11 g36_10 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 rb36 s36 m36 u36 c36
  -- 0xBDE: lw
  obtain ⟨n38, d38, u38⟩ := s37.lw E37.self sv_at_bde (off' := 0xBE2) (by decide)
    (by rw [g37_2, show B + 0x21A0 + 0x31C = B + 0x21A0 + BitVec.ofNat 32 0x31C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s38 : St n38.mem SV n38 0xBE2 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
  have t38 : Steps n0 n38 := t37.trans (.single d38)
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.same m38
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = ((BitVec.ofNat 32 tl32.len).extractLsb' 0 8).zeroExtend 32 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u38.regs, upd_ne (by decide) (by decide), g37_9]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, upd_ne (by decide) (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = x20 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = x21 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = x22 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = x23 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = x24 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = x25 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = x27 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_27]
  have g38_10 : reg n38 a0 = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by
    rw [u38.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g37_2, show B + 0x21A0 + 0x31C = B + 0x21A0 + BitVec.ofNat 32 0x31C by sv_addr, w37_31c]
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB)] := by rw [m38]; exact keep_kk37
  clear keep_kk37
  have w38_2e8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m38]; exact w37_2e8
  have w38_2ec : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m38]; exact w37_2ec
  have w38_300 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m38]; exact w37_300
  have w38_304 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m38]; exact w37_304
  have w38_308 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m38]; exact w37_308
  have w38_30c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m38]; exact w37_30c
  have w38_310 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m38]; exact w37_310
  have w38_314 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m38]; exact w37_314
  have w38_318 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m38]; exact w37_318
  have w38_31c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m38]; exact w37_31c
  have w38_328 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m38]; exact w37_328
  have w38_32c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = BitVec.ofNat 32 tl32.len := by rw [m38]; exact w37_32c
  have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m38]; exact w37_420
  have w38_424 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m38]; exact w37_424
  have w38_428 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m38]; exact w37_428
  have w38_42c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m38]; exact w37_42c
  have b38_325 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x325) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m38]; exact b37_325
  have b38_326 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x326) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m38]; exact b37_326
  have b38_327 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x327) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m38]; exact b37_327
  have b38_424 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m38]; exact b37_424
  have b38_425 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m38]; exact b37_425
  have b38_426 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m38]; exact b37_426
  have b38_427 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m38]; exact b37_427
  clear b37_327 b37_326 b37_325 w37_32c w37_328 b37_427 b37_426 b37_425 b37_424 w37_42c w37_428 w37_424 w37_420 w37_31c w37_318 w37_314 w37_310 w37_30c w37_308 w37_304 w37_300 w37_2ec w37_2e8 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 s37 X37 K37 P37 b36_427 b36_426 b36_425
  -- 0xBE2: sw
  obtain ⟨n39, d39, s39, fr39, K39, W39, rg39⟩ := sv_sw F E38 s38 sv_at_be2 (off' := 0xBE6) (c := 0x320)
    (by decide) (by rw [g38_2]; sv_addr) (by decide) (by decide)
  have t39 : Steps n0 n39 := t38.trans d39
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.keep K39 (by decide)
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [rg39 sp, g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg39 (3 : Fin 32), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg39 (4 : Fin 32), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = ((BitVec.ofNat 32 tl32.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg39 (8 : Fin 32), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [rg39 (9 : Fin 32), g38_9]
  have g39_10 : reg n39 a0 = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [rg39 a0, g38_10]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [rg39 (18 : Fin 32), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [rg39 (19 : Fin 32), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = x20 := by rw [rg39 (20 : Fin 32), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = x21 := by rw [rg39 (21 : Fin 32), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = x22 := by rw [rg39 (22 : Fin 32), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = x23 := by rw [rg39 (23 : Fin 32), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = x24 := by rw [rg39 (24 : Fin 32), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = x25 := by rw [rg39 (25 : Fin 32), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [rg39 (26 : Fin 32), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = x27 := by rw [rg39 (27 : Fin 32), g38_27]
  have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4)] := keep_kk38.trans K39.toL
  clear keep_kk38
  have w39_2e8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K39.w32 (by decide) (by decide)).trans w38_2e8
  have w39_2ec : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K39.w32 (by decide) (by decide)).trans w38_2ec
  have w39_300 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K39.w32 (by decide) (by decide)).trans w38_300
  have w39_304 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K39.w32 (by decide) (by decide)).trans w38_304
  have w39_308 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K39.w32 (by decide) (by decide)).trans w38_308
  have w39_30c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K39.w32 (by decide) (by decide)).trans w38_30c
  have w39_310 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K39.w32 (by decide) (by decide)).trans w38_310
  have w39_314 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := (K39.w32 (by decide) (by decide)).trans w38_314
  have w39_318 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := (K39.w32 (by decide) (by decide)).trans w38_318
  have w39_31c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := (K39.w32 (by decide) (by decide)).trans w38_31c
  have w39_328 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K39.w32 (by decide) (by decide)).trans w38_328
  have w39_32c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = BitVec.ofNat 32 tl32.len := (K39.w32 (by decide) (by decide)).trans w38_32c
  have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K39.w32 (by decide) (by decide)).trans w38_420
  have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := (K39.w32 (by decide) (by decide)).trans w38_424
  have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K39.w32 (by decide) (by decide)).trans w38_428
  have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := (K39.w32 (by decide) (by decide)).trans w38_42c
  have b39_325 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x325) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := (K39.b8 (by decide) (by decide)).trans b38_325
  have b39_326 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x326) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := (K39.b8 (by decide) (by decide)).trans b38_326
  have b39_327 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x327) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := (K39.b8 (by decide) (by decide)).trans b38_327
  have b39_424 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := (K39.b8 (by decide) (by decide)).trans b38_424
  have b39_425 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := (K39.b8 (by decide) (by decide)).trans b38_425
  have b39_426 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := (K39.b8 (by decide) (by decide)).trans b38_426
  have b39_427 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := (K39.b8 (by decide) (by decide)).trans b38_427
  have w39_320 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [W39, g38_9]
  clear b38_427 b38_426 b38_425 b38_424 b38_327 b38_326 b38_325 w38_42c w38_428 w38_424 w38_420 w38_32c w38_328 w38_31c w38_318 w38_314 w38_310 w38_30c w38_308 w38_304 w38_300 w38_2ec w38_2e8 g38_10 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 m38 s38 u38 d38
  -- 0xBE6: sb
  obtain ⟨n40, d40, s40, fr40, K40, W40, rg40⟩ := sv_sb F E39 s39 sv_at_be6 (off' := 0xBEA) (c := 0x324)
    (by decide) (by rw [g39_2]; sv_addr) (by decide)
  have t40 : Steps n0 n40 := t39.trans d40
  have fR40 : ∀ x, SvR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : SvCode n40.mem := E39.fr F fr40
  have V40 : SvSaves B n40.mem v := V39.keep K40 (by decide)
  have g40_2 : reg n40 sp = B + 0x21A0 := by rw [rg40 sp, g39_2]
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg40 (3 : Fin 32), g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg40 (4 : Fin 32), g39_4]
  have g40_8 : reg n40 (8 : Fin 32) = ((BitVec.ofNat 32 tl32.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg40 (8 : Fin 32), g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [rg40 (9 : Fin 32), g39_9]
  have g40_10 : reg n40 a0 = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [rg40 a0, g39_10]
  have g40_18 : reg n40 (18 : Fin 32) = out := by rw [rg40 (18 : Fin 32), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [rg40 (19 : Fin 32), g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = x20 := by rw [rg40 (20 : Fin 32), g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = x21 := by rw [rg40 (21 : Fin 32), g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = x22 := by rw [rg40 (22 : Fin 32), g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = x23 := by rw [rg40 (23 : Fin 32), g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = x24 := by rw [rg40 (24 : Fin 32), g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = x25 := by rw [rg40 (25 : Fin 32), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = x26 := by rw [rg40 (26 : Fin 32), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = x27 := by rw [rg40 (27 : Fin 32), g39_27]
  have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1)] := keep_kk39.trans K40.toL
  clear keep_kk39
  have w40_2e8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K40.w32 (by decide) (by decide)).trans w39_2e8
  have w40_2ec : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K40.w32 (by decide) (by decide)).trans w39_2ec
  have w40_300 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K40.w32 (by decide) (by decide)).trans w39_300
  have w40_304 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K40.w32 (by decide) (by decide)).trans w39_304
  have w40_308 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K40.w32 (by decide) (by decide)).trans w39_308
  have w40_30c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K40.w32 (by decide) (by decide)).trans w39_30c
  have w40_310 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K40.w32 (by decide) (by decide)).trans w39_310
  have w40_314 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := (K40.w32 (by decide) (by decide)).trans w39_314
  have w40_318 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := (K40.w32 (by decide) (by decide)).trans w39_318
  have w40_31c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := (K40.w32 (by decide) (by decide)).trans w39_31c
  have w40_320 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K40.w32 (by decide) (by decide)).trans w39_320
  have w40_328 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K40.w32 (by decide) (by decide)).trans w39_328
  have w40_32c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = BitVec.ofNat 32 tl32.len := (K40.w32 (by decide) (by decide)).trans w39_32c
  have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K40.w32 (by decide) (by decide)).trans w39_420
  have w40_424 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := (K40.w32 (by decide) (by decide)).trans w39_424
  have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K40.w32 (by decide) (by decide)).trans w39_428
  have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := (K40.w32 (by decide) (by decide)).trans w39_42c
  have b40_325 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x325) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := (K40.b8 (by decide) (by decide)).trans b39_325
  have b40_326 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x326) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := (K40.b8 (by decide) (by decide)).trans b39_326
  have b40_327 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x327) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := (K40.b8 (by decide) (by decide)).trans b39_327
  have b40_424 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := (K40.b8 (by decide) (by decide)).trans b39_424
  have b40_425 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := (K40.b8 (by decide) (by decide)).trans b39_425
  have b40_426 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := (K40.b8 (by decide) (by decide)).trans b39_426
  have b40_427 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := (K40.b8 (by decide) (by decide)).trans b39_427
  have b40_324 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [W40, g39_8, lbu_low]
  clear w39_320 b39_427 b39_426 b39_425 b39_424 b39_327 b39_326 b39_325 w39_42c w39_428 w39_424 w39_420 w39_32c w39_328 w39_31c w39_318 w39_314 w39_310 w39_30c w39_308 w39_304 w39_300 w39_2ec w39_2e8 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_10 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 rg39 W39 K39 fr39 s39 d39
  have w40_324 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := ld_of_bytes b40_324
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x324 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x325 by sv_addr]; exact b40_325)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x324 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x326 by sv_addr]; exact b40_326)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x324 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x327 by sv_addr]; exact b40_327)
  by_cases herem : (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) = 0
  rotate_left
  · -- 0xBEA: branch, taken
    obtain ⟨n41, d41, u41⟩ := s40.taken E40.self 0x14C sv_at_bea
      (by decide) (by rw [g40_10, s40.zero]; exact br_bne_t herem)
    have s41 : St n41.mem SV n41 0x14C (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
    have m41 : n41.mem = n40.mem := u41.mem
    have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
    have t41 : Steps n0 n41 := t40.trans (.single d41)
    have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
    have E41 : SvCode n41.mem := E40.fr F fr41
    have V41 : SvSaves B n41.mem v := V40.same m41
    have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
    have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
    have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
    have g41_8 : reg n41 (8 : Fin 32) = ((BitVec.ofNat 32 tl32.len).extractLsb' 0 8).zeroExtend 32 := by rw [u41.regs, g40_8]
    have g41_9 : reg n41 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u41.regs, g40_9]
    have g41_10 : reg n41 a0 = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [u41.regs, g40_10]
    have g41_18 : reg n41 (18 : Fin 32) = out := by rw [u41.regs, g40_18]
    have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [u41.regs, g40_19]
    have g41_20 : reg n41 (20 : Fin 32) = x20 := by rw [u41.regs, g40_20]
    have g41_21 : reg n41 (21 : Fin 32) = x21 := by rw [u41.regs, g40_21]
    have g41_22 : reg n41 (22 : Fin 32) = x22 := by rw [u41.regs, g40_22]
    have g41_23 : reg n41 (23 : Fin 32) = x23 := by rw [u41.regs, g40_23]
    have g41_24 : reg n41 (24 : Fin 32) = x24 := by rw [u41.regs, g40_24]
    have g41_25 : reg n41 (25 : Fin 32) = x25 := by rw [u41.regs, g40_25]
    have g41_26 : reg n41 (26 : Fin 32) = x26 := by rw [u41.regs, g40_26]
    have g41_27 : reg n41 (27 : Fin 32) = x27 := by rw [u41.regs, g40_27]
    have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1)] := by rw [m41]; exact keep_kk40
    clear keep_kk40
    have w41_2e8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m41]; exact w40_2e8
    have w41_2ec : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m41]; exact w40_2ec
    have w41_300 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m41]; exact w40_300
    have w41_304 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m41]; exact w40_304
    have w41_308 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m41]; exact w40_308
    have w41_30c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m41]; exact w40_30c
    have w41_310 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m41]; exact w40_310
    have w41_314 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m41]; exact w40_314
    have w41_318 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m41]; exact w40_318
    have w41_31c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m41]; exact w40_31c
    have w41_320 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m41]; exact w40_320
    have w41_324 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m41]; exact w40_324
    have w41_328 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m41]; exact w40_328
    have w41_32c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = BitVec.ofNat 32 tl32.len := by rw [m41]; exact w40_32c
    have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m41]; exact w40_420
    have w41_424 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m41]; exact w40_424
    have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m41]; exact w40_428
    have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m41]; exact w40_42c
    have b41_424 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m41]; exact b40_424
    have b41_425 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m41]; exact b40_425
    have b41_426 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m41]; exact b40_426
    have b41_427 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m41]; exact b40_427
    clear b40_324 b40_427 b40_426 b40_425 b40_424 b40_327 b40_326 b40_325 w40_42c w40_428 w40_424 w40_420 w40_32c w40_328 w40_320 w40_31c w40_318 w40_314 w40_310 w40_30c w40_308 w40_304 w40_300 w40_2ec w40_2e8 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_10 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 rg40 W40 K40 fr40 s40 d40
    -- 0x14C
    obtain ⟨n42, c42, u42⟩ := s41.block svTr214c E41.self svTr214c_end
      ⟨trivial, trivial⟩
    have m42 : n42.mem = n41.mem := u42.mem
    have s42 : St n42.mem SV n42 0x14E (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
    have rb42 : ∀ q, reg n42 q = (runBlock svTr214c (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
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
    have g42_9 : reg n42 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by
      rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
    have g42_10 : reg n42 a0 = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by
      rw [rb42, runBlock_reg _ _ _ a0 s41.zero (by decide), g41_10]
    have g42_18 : reg n42 (18 : Fin 32) = out := by
      rw [rb42, runBlock_reg _ _ _ (18 : Fin 32) s41.zero (by decide), g41_18]
    have g42_19 : reg n42 (19 : Fin 32) = bp := by
      rw [rb42, runBlock_reg _ _ _ (19 : Fin 32) s41.zero (by decide), g41_19]
    have g42_20 : reg n42 (20 : Fin 32) = x20 := by
      rw [rb42, runBlock_reg _ _ _ (20 : Fin 32) s41.zero (by decide), g41_20]
    have g42_21 : reg n42 (21 : Fin 32) = x21 := by
      rw [rb42, runBlock_reg _ _ _ (21 : Fin 32) s41.zero (by decide), g41_21]
    have g42_22 : reg n42 (22 : Fin 32) = x22 := by
      rw [rb42, runBlock_reg _ _ _ (22 : Fin 32) s41.zero (by decide), g41_22]
    have g42_23 : reg n42 (23 : Fin 32) = x23 := by
      rw [rb42, runBlock_reg _ _ _ (23 : Fin 32) s41.zero (by decide), g41_23]
    have g42_24 : reg n42 (24 : Fin 32) = x24 := by
      rw [rb42, runBlock_reg _ _ _ (24 : Fin 32) s41.zero (by decide), g41_24]
    have g42_25 : reg n42 (25 : Fin 32) = x25 := by
      rw [rb42, runBlock_reg _ _ _ (25 : Fin 32) s41.zero (by decide), g41_25]
    have g42_26 : reg n42 (26 : Fin 32) = x26 := by
      rw [rb42, runBlock_reg _ _ _ (26 : Fin 32) s41.zero (by decide), g41_26]
    have g42_27 : reg n42 (27 : Fin 32) = x27 := by
      rw [rb42, runBlock_reg _ _ _ (27 : Fin 32) s41.zero (by decide), g41_27]
    have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb42]; simp +decide only [runBlock, BInstr.run, svTr214c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1)] := by rw [m42]; exact keep_kk41
    clear keep_kk41
    have w42_2e8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m42]; exact w41_2e8
    have w42_2ec : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m42]; exact w41_2ec
    have w42_300 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m42]; exact w41_300
    have w42_304 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m42]; exact w41_304
    have w42_308 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m42]; exact w41_308
    have w42_30c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m42]; exact w41_30c
    have w42_310 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m42]; exact w41_310
    have w42_314 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m42]; exact w41_314
    have w42_318 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m42]; exact w41_318
    have w42_31c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m42]; exact w41_31c
    have w42_320 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m42]; exact w41_320
    have w42_324 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m42]; exact w41_324
    have w42_328 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m42]; exact w41_328
    have w42_32c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = BitVec.ofNat 32 tl32.len := by rw [m42]; exact w41_32c
    have w42_420 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m42]; exact w41_420
    have w42_424 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m42]; exact w41_424
    have w42_428 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m42]; exact w41_428
    have w42_42c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m42]; exact w41_42c
    have b42_424 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m42]; exact b41_424
    have b42_425 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m42]; exact b41_425
    have b42_426 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m42]; exact b41_426
    have b42_427 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m42]; exact b41_427
    clear b41_427 b41_426 b41_425 b41_424 w41_42c w41_428 w41_424 w41_420 w41_32c w41_328 w41_324 w41_320 w41_31c w41_318 w41_314 w41_310 w41_30c w41_308 w41_304 w41_300 w41_2ec w41_2e8 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
    -- 0x14E: j
    obtain ⟨n43, d43, u43⟩ := s42.jump E42.self sv_at_14e (off' := 0x7A4) (by decide)
      (by rw [s42.pc]; decide)
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
    have g43_8 : reg n43 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u43.regs, g42_8]
    have g43_9 : reg n43 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u43.regs, g42_9]
    have g43_10 : reg n43 a0 = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [u43.regs, g42_10]
    have g43_18 : reg n43 (18 : Fin 32) = out := by rw [u43.regs, g42_18]
    have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [u43.regs, g42_19]
    have g43_20 : reg n43 (20 : Fin 32) = x20 := by rw [u43.regs, g42_20]
    have g43_21 : reg n43 (21 : Fin 32) = x21 := by rw [u43.regs, g42_21]
    have g43_22 : reg n43 (22 : Fin 32) = x22 := by rw [u43.regs, g42_22]
    have g43_23 : reg n43 (23 : Fin 32) = x23 := by rw [u43.regs, g42_23]
    have g43_24 : reg n43 (24 : Fin 32) = x24 := by rw [u43.regs, g42_24]
    have g43_25 : reg n43 (25 : Fin 32) = x25 := by rw [u43.regs, g42_25]
    have g43_26 : reg n43 (26 : Fin 32) = x26 := by rw [u43.regs, g42_26]
    have g43_27 : reg n43 (27 : Fin 32) = x27 := by rw [u43.regs, g42_27]
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1)] := by rw [m43]; exact keep_kk42
    clear keep_kk42
    have w43_2e8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m43]; exact w42_2e8
    have w43_2ec : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m43]; exact w42_2ec
    have w43_300 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m43]; exact w42_300
    have w43_304 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m43]; exact w42_304
    have w43_308 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m43]; exact w42_308
    have w43_30c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m43]; exact w42_30c
    have w43_310 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m43]; exact w42_310
    have w43_314 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m43]; exact w42_314
    have w43_318 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m43]; exact w42_318
    have w43_31c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m43]; exact w42_31c
    have w43_320 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m43]; exact w42_320
    have w43_324 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m43]; exact w42_324
    have w43_328 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m43]; exact w42_328
    have w43_32c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = BitVec.ofNat 32 tl32.len := by rw [m43]; exact w42_32c
    have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m43]; exact w42_420
    have w43_424 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m43]; exact w42_424
    have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m43]; exact w42_428
    have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m43]; exact w42_42c
    have b43_424 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m43]; exact b42_424
    have b43_425 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m43]; exact b42_425
    have b43_426 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m43]; exact b42_426
    have b43_427 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m43]; exact b42_427
    clear b42_427 b42_426 b42_425 b42_424 w42_42c w42_428 w42_424 w42_420 w42_32c w42_328 w42_324 w42_320 w42_31c w42_318 w42_314 w42_310 w42_30c w42_308 w42_304 w42_300 w42_2ec w42_2e8 g42_8 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_10 g42_9 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    exact .inl ⟨(fun ⟨tl2', h0', h1', op13', ol13', h2', to13', h3', h4', tl21', h5', h6', tl32', h7', h8', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [ht13] at h3'; cases h3'; rw [hr21] at h5'; cases h5'; rw [hr32] at h7'; cases h7'; exact herem h8'), sv_fail F E43 s43 t43 (fun x hx => (fR43 x hx).trans (fM x hx).symm) V43 hret g43_2 g43_18 hO g43_3 g43_4 (by rw [g43_8]; sv_code)⟩
  -- 0xBEA: branch, not taken
  obtain ⟨n41, d41, u41⟩ := s40.notTaken E40.self 0xBEE sv_at_bea
    (by decide) (by rw [g40_10, s40.zero]; exact br_bne_f herem)
  have s41 : St n41.mem SV n41 0xBEE (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
  have m41 : n41.mem = n40.mem := u41.mem
  have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
  have t41 : Steps n0 n41 := t40.trans (.single d41)
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.same m41
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = ((BitVec.ofNat 32 tl32.len).extractLsb' 0 8).zeroExtend 32 := by rw [u41.regs, g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u41.regs, g40_9]
  have g41_10 : reg n41 a0 = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [u41.regs, g40_10]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [u41.regs, g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [u41.regs, g40_19]
  have g41_20 : reg n41 (20 : Fin 32) = x20 := by rw [u41.regs, g40_20]
  have g41_21 : reg n41 (21 : Fin 32) = x21 := by rw [u41.regs, g40_21]
  have g41_22 : reg n41 (22 : Fin 32) = x22 := by rw [u41.regs, g40_22]
  have g41_23 : reg n41 (23 : Fin 32) = x23 := by rw [u41.regs, g40_23]
  have g41_24 : reg n41 (24 : Fin 32) = x24 := by rw [u41.regs, g40_24]
  have g41_25 : reg n41 (25 : Fin 32) = x25 := by rw [u41.regs, g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = x26 := by rw [u41.regs, g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = x27 := by rw [u41.regs, g40_27]
  have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1)] := by rw [m41]; exact keep_kk40
  clear keep_kk40
  have w41_2e8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m41]; exact w40_2e8
  have w41_2ec : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m41]; exact w40_2ec
  have w41_300 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m41]; exact w40_300
  have w41_304 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m41]; exact w40_304
  have w41_308 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m41]; exact w40_308
  have w41_30c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m41]; exact w40_30c
  have w41_310 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m41]; exact w40_310
  have w41_314 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m41]; exact w40_314
  have w41_318 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m41]; exact w40_318
  have w41_31c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m41]; exact w40_31c
  have w41_320 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m41]; exact w40_320
  have w41_324 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m41]; exact w40_324
  have w41_328 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m41]; exact w40_328
  have w41_32c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = BitVec.ofNat 32 tl32.len := by rw [m41]; exact w40_32c
  have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m41]; exact w40_420
  have w41_424 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m41]; exact w40_424
  have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m41]; exact w40_428
  have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m41]; exact w40_42c
  have b41_424 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m41]; exact b40_424
  have b41_425 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m41]; exact b40_425
  have b41_426 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m41]; exact b40_426
  have b41_427 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m41]; exact b40_427
  clear b40_324 b40_427 b40_426 b40_425 b40_424 b40_327 b40_326 b40_325 w40_42c w40_428 w40_424 w40_420 w40_32c w40_328 w40_320 w40_31c w40_318 w40_314 w40_310 w40_30c w40_308 w40_304 w40_300 w40_2ec w40_2e8 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_10 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 rg40 W40 K40 fr40 s40 d40
  -- 0xBEE
  obtain ⟨n42, c42, u42⟩ := s41.block svTr2bee E41.self svTr2bee_end
    ⟨trivial, trivial, trivial⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have s42 : St n42.mem SV n42 0xBF2 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have rb42 : ∀ q, reg n42 q = (runBlock svTr2bee (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
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
  have g42_8 : reg n42 (8 : Fin 32) = ((BitVec.ofNat 32 tl32.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb42, runBlock_reg _ _ _ (8 : Fin 32) s41.zero (by decide), g41_8]
  have g42_9 : reg n42 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by
    rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
  have g42_18 : reg n42 (18 : Fin 32) = out := by
    rw [rb42, runBlock_reg _ _ _ (18 : Fin 32) s41.zero (by decide), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by
    rw [rb42, runBlock_reg _ _ _ (19 : Fin 32) s41.zero (by decide), g41_19]
  have g42_20 : reg n42 (20 : Fin 32) = x20 := by
    rw [rb42, runBlock_reg _ _ _ (20 : Fin 32) s41.zero (by decide), g41_20]
  have g42_21 : reg n42 (21 : Fin 32) = x21 := by
    rw [rb42, runBlock_reg _ _ _ (21 : Fin 32) s41.zero (by decide), g41_21]
  have g42_22 : reg n42 (22 : Fin 32) = x22 := by
    rw [rb42, runBlock_reg _ _ _ (22 : Fin 32) s41.zero (by decide), g41_22]
  have g42_23 : reg n42 (23 : Fin 32) = x23 := by
    rw [rb42, runBlock_reg _ _ _ (23 : Fin 32) s41.zero (by decide), g41_23]
  have g42_24 : reg n42 (24 : Fin 32) = x24 := by
    rw [rb42, runBlock_reg _ _ _ (24 : Fin 32) s41.zero (by decide), g41_24]
  have g42_25 : reg n42 (25 : Fin 32) = x25 := by
    rw [rb42, runBlock_reg _ _ _ (25 : Fin 32) s41.zero (by decide), g41_25]
  have g42_26 : reg n42 (26 : Fin 32) = x26 := by
    rw [rb42, runBlock_reg _ _ _ (26 : Fin 32) s41.zero (by decide), g41_26]
  have g42_27 : reg n42 (27 : Fin 32) = x27 := by
    rw [rb42, runBlock_reg _ _ _ (27 : Fin 32) s41.zero (by decide), g41_27]
  have g42_10 : reg n42 a0 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svTr2bee, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g42_11 : reg n42 a1 = BitVec.ofNat 32 0x3 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svTr2bee, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1)] := by rw [m42]; exact keep_kk41
  clear keep_kk41
  have w42_2e8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m42]; exact w41_2e8
  have w42_2ec : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m42]; exact w41_2ec
  have w42_300 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m42]; exact w41_300
  have w42_304 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m42]; exact w41_304
  have w42_308 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m42]; exact w41_308
  have w42_30c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m42]; exact w41_30c
  have w42_310 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m42]; exact w41_310
  have w42_314 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m42]; exact w41_314
  have w42_318 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m42]; exact w41_318
  have w42_31c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m42]; exact w41_31c
  have w42_320 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m42]; exact w41_320
  have w42_324 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m42]; exact w41_324
  have w42_328 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m42]; exact w41_328
  have w42_32c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = BitVec.ofNat 32 tl32.len := by rw [m42]; exact w41_32c
  have w42_420 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m42]; exact w41_420
  have w42_424 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m42]; exact w41_424
  have w42_428 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m42]; exact w41_428
  have w42_42c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m42]; exact w41_42c
  have b42_424 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m42]; exact b41_424
  have b42_425 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m42]; exact b41_425
  have b42_426 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m42]; exact b41_426
  have b42_427 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m42]; exact b41_427
  clear b41_427 b41_426 b41_425 b41_424 w41_42c w41_428 w41_424 w41_420 w41_32c w41_328 w41_324 w41_320 w41_31c w41_318 w41_314 w41_310 w41_30c w41_308 w41_304 w41_300 w41_2ec w41_2e8 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41 w40_324
  -- 0xBF2: sv_iiF
  obtain ⟨n43, c43, s43, sp43, rk43, K43, A43, R43, fr43⟩ := sv_iiF (dc := 0x320)
    F E42 s42 sv_at_bf2 sv_at_bf6 (by decide) (by decide) g42_2 g42_10
    (by decide) (by decide) w42_328 w42_32c ((((r_in.contentW hr2).restW (derOid_ok_elem ht13)).contentW hr21).contentW hr32)
  have t43 : Steps n0 n43 := t42.trans c43
  have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.keepL K43 (by decide)
  rw [sv_mb fR42 ((((r_in.contentW hr2).restW (derOid_ok_elem ht13)).contentW hr21).contentW hr32), derIntIsOf_congr fR42 ((((r_in.contentW hr2).restW (derOid_ok_elem ht13)).contentW hr21).contentW hr32), g42_11] at R43
  rw [sv_mb fR42 ((((r_in.contentW hr2).restW (derOid_ok_elem ht13)).contentW hr21).contentW hr32)] at A43
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk43 (3 : Fin 32) (by decide), g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk43 (4 : Fin 32) (by decide), g42_4]
  have g43_8 : reg n43 (8 : Fin 32) = ((BitVec.ofNat 32 tl32.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk43 (8 : Fin 32) (by decide), g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [rk43 (9 : Fin 32) (by decide), g42_9]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [rk43 (18 : Fin 32) (by decide), g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [rk43 (19 : Fin 32) (by decide), g42_19]
  have g43_20 : reg n43 (20 : Fin 32) = x20 := by rw [rk43 (20 : Fin 32) (by decide), g42_20]
  have g43_21 : reg n43 (21 : Fin 32) = x21 := by rw [rk43 (21 : Fin 32) (by decide), g42_21]
  have g43_22 : reg n43 (22 : Fin 32) = x22 := by rw [rk43 (22 : Fin 32) (by decide), g42_22]
  have g43_23 : reg n43 (23 : Fin 32) = x23 := by rw [rk43 (23 : Fin 32) (by decide), g42_23]
  have g43_24 : reg n43 (24 : Fin 32) = x24 := by rw [rk43 (24 : Fin 32) (by decide), g42_24]
  have g43_25 : reg n43 (25 : Fin 32) = x25 := by rw [rk43 (25 : Fin 32) (by decide), g42_25]
  have g43_26 : reg n43 (26 : Fin 32) = x26 := by rw [rk43 (26 : Fin 32) (by decide), g42_26]
  have g43_27 : reg n43 (27 : Fin 32) = x27 := by rw [rk43 (27 : Fin 32) (by decide), g42_27]
  have g43_2 : reg n43 sp = B + 0x21A0 := sp43
  obtain ⟨r43, hr43⟩ : ∃ r, derIntIsOf M0 (memBytes M0 (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) (BitVec.ofNat 32 tl32.len).toNat) (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) (derElement 2 (memBytes M0 (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) (BitVec.ofNat 32 tl32.len).toNat)) ((BitVec.ofNat 32 0x3).extractLsb' 0 8) = r := ⟨_, rfl⟩
  rcases r43 with b43 | (_ | _)
  · rw [hr43] at R43
    obtain ⟨a0_43, a1_43⟩ := R43
    have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x1 := a0_43
    have hz_c43 : ((reg n43 a1).extractLsb' 0 8).toNat < 0x27 := by
      rw [a1_43]; exact derIntIsOf_err_lt hr43
    have g43_11 : reg n43 a1 = reg n43 a1 := rfl
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := keep_kk42.trans K43
    clear keep_kk42
    have w43_2e8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K43.w32 (by decide) (by decide)).trans w42_2e8
    have w43_2ec : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K43.w32 (by decide) (by decide)).trans w42_2ec
    have w43_300 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K43.w32 (by decide) (by decide)).trans w42_300
    have w43_304 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K43.w32 (by decide) (by decide)).trans w42_304
    have w43_308 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K43.w32 (by decide) (by decide)).trans w42_308
    have w43_30c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K43.w32 (by decide) (by decide)).trans w42_30c
    have w43_310 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K43.w32 (by decide) (by decide)).trans w42_310
    have w43_314 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := (K43.w32 (by decide) (by decide)).trans w42_314
    have w43_318 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := (K43.w32 (by decide) (by decide)).trans w42_318
    have w43_31c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := (K43.w32 (by decide) (by decide)).trans w42_31c
    have w43_320 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K43.w32 (by decide) (by decide)).trans w42_320
    have w43_324 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := (K43.w32 (by decide) (by decide)).trans w42_324
    have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K43.w32 (by decide) (by decide)).trans w42_420
    have w43_424 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := (K43.w32 (by decide) (by decide)).trans w42_424
    have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K43.w32 (by decide) (by decide)).trans w42_428
    have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := (K43.w32 (by decide) (by decide)).trans w42_42c
    have b43_424 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := (K43.b8 (by decide) (by decide)).trans b42_424
    have b43_425 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := (K43.b8 (by decide) (by decide)).trans b42_425
    have b43_426 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := (K43.b8 (by decide) (by decide)).trans b42_426
    have b43_427 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := (K43.b8 (by decide) (by decide)).trans b42_427
    clear b42_427 b42_426 b42_425 b42_424 w42_42c w42_428 w42_424 w42_420 w42_32c w42_328 w42_324 w42_320 w42_31c w42_318 w42_314 w42_310 w42_30c w42_308 w42_304 w42_300 w42_2ec w42_2e8 g42_11 g42_10 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    -- 0xBFA
    obtain ⟨n44, c44, u44⟩ := s43.block svTr2bfa E43.self svTr2bfa_end
      ⟨trivial, trivial, trivial⟩
    have m44 : n44.mem = n43.mem := u44.mem
    have s44 : St n44.mem SV n44 0xBFE (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
    have rb44 : ∀ q, reg n44 q = (runBlock svTr2bfa (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
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
    have g44_9 : reg n44 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by
      rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
    have g44_11 : reg n44 a1 = reg n43 a1 := by
      rw [rb44, runBlock_reg _ _ _ a1 s43.zero (by decide), g43_11]
    have g44_18 : reg n44 (18 : Fin 32) = out := by
      rw [rb44, runBlock_reg _ _ _ (18 : Fin 32) s43.zero (by decide), g43_18]
    have g44_19 : reg n44 (19 : Fin 32) = bp := by
      rw [rb44, runBlock_reg _ _ _ (19 : Fin 32) s43.zero (by decide), g43_19]
    have g44_20 : reg n44 (20 : Fin 32) = x20 := by
      rw [rb44, runBlock_reg _ _ _ (20 : Fin 32) s43.zero (by decide), g43_20]
    have g44_21 : reg n44 (21 : Fin 32) = x21 := by
      rw [rb44, runBlock_reg _ _ _ (21 : Fin 32) s43.zero (by decide), g43_21]
    have g44_22 : reg n44 (22 : Fin 32) = x22 := by
      rw [rb44, runBlock_reg _ _ _ (22 : Fin 32) s43.zero (by decide), g43_22]
    have g44_23 : reg n44 (23 : Fin 32) = x23 := by
      rw [rb44, runBlock_reg _ _ _ (23 : Fin 32) s43.zero (by decide), g43_23]
    have g44_24 : reg n44 (24 : Fin 32) = x24 := by
      rw [rb44, runBlock_reg _ _ _ (24 : Fin 32) s43.zero (by decide), g43_24]
    have g44_25 : reg n44 (25 : Fin 32) = x25 := by
      rw [rb44, runBlock_reg _ _ _ (25 : Fin 32) s43.zero (by decide), g43_25]
    have g44_26 : reg n44 (26 : Fin 32) = x26 := by
      rw [rb44, runBlock_reg _ _ _ (26 : Fin 32) s43.zero (by decide), g43_26]
    have g44_27 : reg n44 (27 : Fin 32) = x27 := by
      rw [rb44, runBlock_reg _ _ _ (27 : Fin 32) s43.zero (by decide), g43_27]
    have g44_8 : reg n44 (8 : Fin 32) = reg n43 a1 := by
      rw [rb44]; simp +decide only [runBlock, BInstr.run, svTr2bfa, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb44]; simp +decide only [runBlock, BInstr.run, svTr2bfa, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m44]; exact keep_kk43
    clear keep_kk43
    have w44_2e8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m44]; exact w43_2e8
    have w44_2ec : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m44]; exact w43_2ec
    have w44_300 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m44]; exact w43_300
    have w44_304 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m44]; exact w43_304
    have w44_308 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m44]; exact w43_308
    have w44_30c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m44]; exact w43_30c
    have w44_310 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m44]; exact w43_310
    have w44_314 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m44]; exact w43_314
    have w44_318 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m44]; exact w43_318
    have w44_31c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m44]; exact w43_31c
    have w44_320 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m44]; exact w43_320
    have w44_324 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m44]; exact w43_324
    have w44_420 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m44]; exact w43_420
    have w44_424 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m44]; exact w43_424
    have w44_428 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m44]; exact w43_428
    have w44_42c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m44]; exact w43_42c
    have b44_424 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m44]; exact b43_424
    have b44_425 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m44]; exact b43_425
    have b44_426 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m44]; exact b43_426
    have b44_427 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m44]; exact b43_427
    clear b43_427 b43_426 b43_425 b43_424 w43_42c w43_428 w43_424 w43_420 w43_324 w43_320 w43_31c w43_318 w43_314 w43_310 w43_30c w43_308 w43_304 w43_300 w43_2ec w43_2e8 g43_11 g43_10 a1_43 a0_43
    -- 0xBFE: branch, taken
    obtain ⟨n45, d45, u45⟩ := s44.taken E44.self 0x7A4 sv_at_bfe
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
    have g45_8 : reg n45 (8 : Fin 32) = reg n43 a1 := by rw [u45.regs, g44_8]
    have g45_9 : reg n45 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u45.regs, g44_9]
    have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_10]
    have g45_11 : reg n45 a1 = reg n43 a1 := by rw [u45.regs, g44_11]
    have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
    have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
    have g45_20 : reg n45 (20 : Fin 32) = x20 := by rw [u45.regs, g44_20]
    have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [u45.regs, g44_21]
    have g45_22 : reg n45 (22 : Fin 32) = x22 := by rw [u45.regs, g44_22]
    have g45_23 : reg n45 (23 : Fin 32) = x23 := by rw [u45.regs, g44_23]
    have g45_24 : reg n45 (24 : Fin 32) = x24 := by rw [u45.regs, g44_24]
    have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [u45.regs, g44_25]
    have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [u45.regs, g44_26]
    have g45_27 : reg n45 (27 : Fin 32) = x27 := by rw [u45.regs, g44_27]
    have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m45]; exact keep_kk44
    clear keep_kk44
    have w45_2e8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m45]; exact w44_2e8
    have w45_2ec : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m45]; exact w44_2ec
    have w45_300 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m45]; exact w44_300
    have w45_304 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m45]; exact w44_304
    have w45_308 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m45]; exact w44_308
    have w45_30c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m45]; exact w44_30c
    have w45_310 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m45]; exact w44_310
    have w45_314 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m45]; exact w44_314
    have w45_318 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m45]; exact w44_318
    have w45_31c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m45]; exact w44_31c
    have w45_320 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m45]; exact w44_320
    have w45_324 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m45]; exact w44_324
    have w45_420 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m45]; exact w44_420
    have w45_424 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m45]; exact w44_424
    have w45_428 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m45]; exact w44_428
    have w45_42c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m45]; exact w44_42c
    have b45_424 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m45]; exact b44_424
    have b45_425 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m45]; exact b44_425
    have b45_426 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m45]; exact b44_426
    have b45_427 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m45]; exact b44_427
    clear b44_427 b44_426 b44_425 b44_424 w44_42c w44_428 w44_424 w44_420 w44_324 w44_320 w44_31c w44_318 w44_314 w44_310 w44_30c w44_308 w44_304 w44_300 w44_2ec w44_2e8 g44_10 g44_8 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_11 g44_9 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
    exact .inl ⟨(fun ⟨tl2', h0', h1', op13', ol13', h2', to13', h3', h4', tl21', h5', h6', tl32', h7', h8', h9', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [ht13] at h3'; cases h3'; rw [hr21] at h5'; cases h5'; rw [hr32] at h7'; cases h7'; rw [hr43] at h9'; cases h9'), sv_fail F E45 s45 t45 (fun x hx => (fR45 x hx).trans (fM x hx).symm) V45 hret g45_2 g45_18 hO g45_3 g45_4 (by rw [g45_8]; sv_code)⟩
  · rw [hr43] at R43
    obtain ⟨a0_43, a1_43⟩ := R43
    have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x0 := a0_43
    have g43_11 : reg n43 a1 = BitVec.ofNat 32 0x0 := by rw [a1_43]; rfl
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := keep_kk42.trans K43
    clear keep_kk42
    have w43_2e8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K43.w32 (by decide) (by decide)).trans w42_2e8
    have w43_2ec : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K43.w32 (by decide) (by decide)).trans w42_2ec
    have w43_300 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K43.w32 (by decide) (by decide)).trans w42_300
    have w43_304 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K43.w32 (by decide) (by decide)).trans w42_304
    have w43_308 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K43.w32 (by decide) (by decide)).trans w42_308
    have w43_30c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K43.w32 (by decide) (by decide)).trans w42_30c
    have w43_310 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K43.w32 (by decide) (by decide)).trans w42_310
    have w43_314 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := (K43.w32 (by decide) (by decide)).trans w42_314
    have w43_318 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := (K43.w32 (by decide) (by decide)).trans w42_318
    have w43_31c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := (K43.w32 (by decide) (by decide)).trans w42_31c
    have w43_320 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K43.w32 (by decide) (by decide)).trans w42_320
    have w43_324 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := (K43.w32 (by decide) (by decide)).trans w42_324
    have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K43.w32 (by decide) (by decide)).trans w42_420
    have w43_424 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := (K43.w32 (by decide) (by decide)).trans w42_424
    have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K43.w32 (by decide) (by decide)).trans w42_428
    have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := (K43.w32 (by decide) (by decide)).trans w42_42c
    have b43_424 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := (K43.b8 (by decide) (by decide)).trans b42_424
    have b43_425 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := (K43.b8 (by decide) (by decide)).trans b42_425
    have b43_426 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := (K43.b8 (by decide) (by decide)).trans b42_426
    have b43_427 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := (K43.b8 (by decide) (by decide)).trans b42_427
    clear b42_427 b42_426 b42_425 b42_424 w42_42c w42_428 w42_424 w42_420 w42_32c w42_328 w42_324 w42_320 w42_31c w42_318 w42_314 w42_310 w42_30c w42_308 w42_304 w42_300 w42_2ec w42_2e8 g42_11 g42_10 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    -- 0xBFA
    obtain ⟨n44, c44, u44⟩ := s43.block svTr2bfa E43.self svTr2bfa_end
      ⟨trivial, trivial, trivial⟩
    have m44 : n44.mem = n43.mem := u44.mem
    have s44 : St n44.mem SV n44 0xBFE (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
    have rb44 : ∀ q, reg n44 q = (runBlock svTr2bfa (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
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
    have g44_9 : reg n44 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by
      rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
    have g44_11 : reg n44 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb44, runBlock_reg _ _ _ a1 s43.zero (by decide), g43_11]
    have g44_18 : reg n44 (18 : Fin 32) = out := by
      rw [rb44, runBlock_reg _ _ _ (18 : Fin 32) s43.zero (by decide), g43_18]
    have g44_19 : reg n44 (19 : Fin 32) = bp := by
      rw [rb44, runBlock_reg _ _ _ (19 : Fin 32) s43.zero (by decide), g43_19]
    have g44_20 : reg n44 (20 : Fin 32) = x20 := by
      rw [rb44, runBlock_reg _ _ _ (20 : Fin 32) s43.zero (by decide), g43_20]
    have g44_21 : reg n44 (21 : Fin 32) = x21 := by
      rw [rb44, runBlock_reg _ _ _ (21 : Fin 32) s43.zero (by decide), g43_21]
    have g44_22 : reg n44 (22 : Fin 32) = x22 := by
      rw [rb44, runBlock_reg _ _ _ (22 : Fin 32) s43.zero (by decide), g43_22]
    have g44_23 : reg n44 (23 : Fin 32) = x23 := by
      rw [rb44, runBlock_reg _ _ _ (23 : Fin 32) s43.zero (by decide), g43_23]
    have g44_24 : reg n44 (24 : Fin 32) = x24 := by
      rw [rb44, runBlock_reg _ _ _ (24 : Fin 32) s43.zero (by decide), g43_24]
    have g44_25 : reg n44 (25 : Fin 32) = x25 := by
      rw [rb44, runBlock_reg _ _ _ (25 : Fin 32) s43.zero (by decide), g43_25]
    have g44_26 : reg n44 (26 : Fin 32) = x26 := by
      rw [rb44, runBlock_reg _ _ _ (26 : Fin 32) s43.zero (by decide), g43_26]
    have g44_27 : reg n44 (27 : Fin 32) = x27 := by
      rw [rb44, runBlock_reg _ _ _ (27 : Fin 32) s43.zero (by decide), g43_27]
    have g44_8 : reg n44 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb44]; simp +decide only [runBlock, BInstr.run, svTr2bfa, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb44]; simp +decide only [runBlock, BInstr.run, svTr2bfa, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m44]; exact keep_kk43
    clear keep_kk43
    have w44_2e8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m44]; exact w43_2e8
    have w44_2ec : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m44]; exact w43_2ec
    have w44_300 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m44]; exact w43_300
    have w44_304 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m44]; exact w43_304
    have w44_308 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m44]; exact w43_308
    have w44_30c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m44]; exact w43_30c
    have w44_310 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m44]; exact w43_310
    have w44_314 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m44]; exact w43_314
    have w44_318 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m44]; exact w43_318
    have w44_31c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m44]; exact w43_31c
    have w44_320 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m44]; exact w43_320
    have w44_324 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m44]; exact w43_324
    have w44_420 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m44]; exact w43_420
    have w44_424 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m44]; exact w43_424
    have w44_428 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m44]; exact w43_428
    have w44_42c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m44]; exact w43_42c
    have b44_424 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m44]; exact b43_424
    have b44_425 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m44]; exact b43_425
    have b44_426 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m44]; exact b43_426
    have b44_427 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m44]; exact b43_427
    clear b43_427 b43_426 b43_425 b43_424 w43_42c w43_428 w43_424 w43_420 w43_324 w43_320 w43_31c w43_318 w43_314 w43_310 w43_30c w43_308 w43_304 w43_300 w43_2ec w43_2e8 g43_11 g43_10 a1_43 a0_43
    -- 0xBFE: branch, not taken
    obtain ⟨n45, d45, u45⟩ := s44.notTaken E44.self 0xC02 sv_at_bfe
      (by decide) (by rw [g44_10, s44.zero]; decide)
    have s45 : St n45.mem SV n45 0xC02 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
    have m45 : n45.mem = n44.mem := u45.mem
    have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
    have t45 : Steps n0 n45 := t44.trans (.single d45)
    have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
    have E45 : SvCode n45.mem := E44.fr F fr45
    have V45 : SvSaves B n45.mem v := V44.same m45
    have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, g44_2]
    have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, g44_3]
    have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, g44_4]
    have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u45.regs, g44_8]
    have g45_9 : reg n45 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u45.regs, g44_9]
    have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x0 := by rw [u45.regs, g44_10]
    have g45_11 : reg n45 a1 = BitVec.ofNat 32 0x0 := by rw [u45.regs, g44_11]
    have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
    have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
    have g45_20 : reg n45 (20 : Fin 32) = x20 := by rw [u45.regs, g44_20]
    have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [u45.regs, g44_21]
    have g45_22 : reg n45 (22 : Fin 32) = x22 := by rw [u45.regs, g44_22]
    have g45_23 : reg n45 (23 : Fin 32) = x23 := by rw [u45.regs, g44_23]
    have g45_24 : reg n45 (24 : Fin 32) = x24 := by rw [u45.regs, g44_24]
    have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [u45.regs, g44_25]
    have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [u45.regs, g44_26]
    have g45_27 : reg n45 (27 : Fin 32) = x27 := by rw [u45.regs, g44_27]
    have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m45]; exact keep_kk44
    clear keep_kk44
    have w45_2e8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m45]; exact w44_2e8
    have w45_2ec : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m45]; exact w44_2ec
    have w45_300 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m45]; exact w44_300
    have w45_304 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m45]; exact w44_304
    have w45_308 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m45]; exact w44_308
    have w45_30c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m45]; exact w44_30c
    have w45_310 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m45]; exact w44_310
    have w45_314 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m45]; exact w44_314
    have w45_318 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m45]; exact w44_318
    have w45_31c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m45]; exact w44_31c
    have w45_320 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m45]; exact w44_320
    have w45_324 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m45]; exact w44_324
    have w45_420 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m45]; exact w44_420
    have w45_424 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m45]; exact w44_424
    have w45_428 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m45]; exact w44_428
    have w45_42c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m45]; exact w44_42c
    have b45_424 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m45]; exact b44_424
    have b45_425 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m45]; exact b44_425
    have b45_426 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m45]; exact b44_426
    have b45_427 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m45]; exact b44_427
    clear b44_427 b44_426 b44_425 b44_424 w44_42c w44_428 w44_424 w44_420 w44_324 w44_320 w44_31c w44_318 w44_314 w44_310 w44_30c w44_308 w44_304 w44_300 w44_2ec w44_2e8 g44_10 g44_8 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_11 g44_9 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
    -- 0xC02
    obtain ⟨n46, c46, u46⟩ := s45.block svTr2c02 E45.self svTr2c02_end
      ⟨trivial, trivial⟩
    have m46 : n46.mem = n45.mem := u46.mem
    have s46 : St n46.mem SV n46 0xC04 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
    have rb46 : ∀ q, reg n46 q = (runBlock svTr2c02 (n45.mem, reg n45)).2 q := fun q => by rw [u46.regs]
    have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
    have t46 : Steps n0 n46 := t45.trans c46
    have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
    have E46 : SvCode n46.mem := E45.fr F fr46
    have V46 : SvSaves B n46.mem v := V45.same m46
    have g46_2 : reg n46 sp = B + 0x21A0 := by
      rw [rb46, runBlock_reg _ _ _ sp s45.zero (by decide), g45_2]
    have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb46, runBlock_reg _ _ _ (3 : Fin 32) s45.zero (by decide), g45_3]
    have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb46, runBlock_reg _ _ _ (4 : Fin 32) s45.zero (by decide), g45_4]
    have g46_9 : reg n46 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by
      rw [rb46, runBlock_reg _ _ _ (9 : Fin 32) s45.zero (by decide), g45_9]
    have g46_10 : reg n46 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb46, runBlock_reg _ _ _ a0 s45.zero (by decide), g45_10]
    have g46_11 : reg n46 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb46, runBlock_reg _ _ _ a1 s45.zero (by decide), g45_11]
    have g46_18 : reg n46 (18 : Fin 32) = out := by
      rw [rb46, runBlock_reg _ _ _ (18 : Fin 32) s45.zero (by decide), g45_18]
    have g46_19 : reg n46 (19 : Fin 32) = bp := by
      rw [rb46, runBlock_reg _ _ _ (19 : Fin 32) s45.zero (by decide), g45_19]
    have g46_20 : reg n46 (20 : Fin 32) = x20 := by
      rw [rb46, runBlock_reg _ _ _ (20 : Fin 32) s45.zero (by decide), g45_20]
    have g46_21 : reg n46 (21 : Fin 32) = x21 := by
      rw [rb46, runBlock_reg _ _ _ (21 : Fin 32) s45.zero (by decide), g45_21]
    have g46_22 : reg n46 (22 : Fin 32) = x22 := by
      rw [rb46, runBlock_reg _ _ _ (22 : Fin 32) s45.zero (by decide), g45_22]
    have g46_23 : reg n46 (23 : Fin 32) = x23 := by
      rw [rb46, runBlock_reg _ _ _ (23 : Fin 32) s45.zero (by decide), g45_23]
    have g46_24 : reg n46 (24 : Fin 32) = x24 := by
      rw [rb46, runBlock_reg _ _ _ (24 : Fin 32) s45.zero (by decide), g45_24]
    have g46_25 : reg n46 (25 : Fin 32) = x25 := by
      rw [rb46, runBlock_reg _ _ _ (25 : Fin 32) s45.zero (by decide), g45_25]
    have g46_26 : reg n46 (26 : Fin 32) = x26 := by
      rw [rb46, runBlock_reg _ _ _ (26 : Fin 32) s45.zero (by decide), g45_26]
    have g46_27 : reg n46 (27 : Fin 32) = x27 := by
      rw [rb46, runBlock_reg _ _ _ (27 : Fin 32) s45.zero (by decide), g45_27]
    have g46_8 : reg n46 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb46]; simp +decide only [runBlock, BInstr.run, svTr2c02, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g45_2, g45_3, g45_4, g45_8, g45_9, g45_10, g45_11, g45_18, g45_19, g45_20, g45_21, g45_22, g45_23, g45_24, g45_25, g45_26, g45_27, s45.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m46]; exact keep_kk45
    clear keep_kk45
    have w46_2e8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m46]; exact w45_2e8
    have w46_2ec : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m46]; exact w45_2ec
    have w46_300 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m46]; exact w45_300
    have w46_304 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m46]; exact w45_304
    have w46_308 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m46]; exact w45_308
    have w46_30c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m46]; exact w45_30c
    have w46_310 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m46]; exact w45_310
    have w46_314 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m46]; exact w45_314
    have w46_318 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m46]; exact w45_318
    have w46_31c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m46]; exact w45_31c
    have w46_320 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m46]; exact w45_320
    have w46_324 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m46]; exact w45_324
    have w46_420 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m46]; exact w45_420
    have w46_424 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m46]; exact w45_424
    have w46_428 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m46]; exact w45_428
    have w46_42c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m46]; exact w45_42c
    have b46_424 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m46]; exact b45_424
    have b46_425 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m46]; exact b45_425
    have b46_426 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m46]; exact b45_426
    have b46_427 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m46]; exact b45_427
    clear b45_427 b45_426 b45_425 b45_424 w45_42c w45_428 w45_424 w45_420 w45_324 w45_320 w45_31c w45_318 w45_314 w45_310 w45_30c w45_308 w45_304 w45_300 w45_2ec w45_2e8 g45_27 g45_26 g45_25 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_11 g45_10 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45
    -- 0xC04: branch, taken
    obtain ⟨n47, d47, u47⟩ := s46.taken E46.self 0x12B8 sv_at_c04
      (by decide) (by rw [g46_8, s46.zero]; decide)
    have s47 : St n47.mem SV n47 0x12B8 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
    have m47 : n47.mem = n46.mem := u47.mem
    have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
    have t47 : Steps n0 n47 := t46.trans (.single d47)
    have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
    have E47 : SvCode n47.mem := E46.fr F fr47
    have V47 : SvSaves B n47.mem v := V46.same m47
    have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
    have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
    have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
    have g47_8 : reg n47 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u47.regs, g46_8]
    have g47_9 : reg n47 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u47.regs, g46_9]
    have g47_10 : reg n47 a0 = BitVec.ofNat 32 0x0 := by rw [u47.regs, g46_10]
    have g47_11 : reg n47 a1 = BitVec.ofNat 32 0x0 := by rw [u47.regs, g46_11]
    have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
    have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
    have g47_20 : reg n47 (20 : Fin 32) = x20 := by rw [u47.regs, g46_20]
    have g47_21 : reg n47 (21 : Fin 32) = x21 := by rw [u47.regs, g46_21]
    have g47_22 : reg n47 (22 : Fin 32) = x22 := by rw [u47.regs, g46_22]
    have g47_23 : reg n47 (23 : Fin 32) = x23 := by rw [u47.regs, g46_23]
    have g47_24 : reg n47 (24 : Fin 32) = x24 := by rw [u47.regs, g46_24]
    have g47_25 : reg n47 (25 : Fin 32) = x25 := by rw [u47.regs, g46_25]
    have g47_26 : reg n47 (26 : Fin 32) = x26 := by rw [u47.regs, g46_26]
    have g47_27 : reg n47 (27 : Fin 32) = x27 := by rw [u47.regs, g46_27]
    have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m47]; exact keep_kk46
    clear keep_kk46
    have w47_2e8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m47]; exact w46_2e8
    have w47_2ec : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m47]; exact w46_2ec
    have w47_300 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m47]; exact w46_300
    have w47_304 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m47]; exact w46_304
    have w47_308 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m47]; exact w46_308
    have w47_30c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m47]; exact w46_30c
    have w47_310 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m47]; exact w46_310
    have w47_314 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m47]; exact w46_314
    have w47_318 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m47]; exact w46_318
    have w47_31c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m47]; exact w46_31c
    have w47_320 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m47]; exact w46_320
    have w47_324 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m47]; exact w46_324
    have w47_420 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m47]; exact w46_420
    have w47_424 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m47]; exact w46_424
    have w47_428 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m47]; exact w46_428
    have w47_42c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m47]; exact w46_42c
    have b47_424 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m47]; exact b46_424
    have b47_425 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m47]; exact b46_425
    have b47_426 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m47]; exact b46_426
    have b47_427 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m47]; exact b46_427
    clear b46_427 b46_426 b46_425 b46_424 w46_42c w46_428 w46_424 w46_420 w46_324 w46_320 w46_31c w46_318 w46_314 w46_310 w46_30c w46_308 w46_304 w46_300 w46_2ec w46_2e8 g46_8 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_11 g46_10 g46_9 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 rb46 s46 m46 u46 c46
    -- 0x12B8
    obtain ⟨n48, c48, u48⟩ := s47.block svTr212b8 E47.self svTr212b8_end
      ⟨trivial, trivial⟩
    have m48 : n48.mem = n47.mem := u48.mem
    have s48 : St n48.mem SV n48 0x12BA (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
    have rb48 : ∀ q, reg n48 q = (runBlock svTr212b8 (n47.mem, reg n47)).2 q := fun q => by rw [u48.regs]
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
    have g48_9 : reg n48 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by
      rw [rb48, runBlock_reg _ _ _ (9 : Fin 32) s47.zero (by decide), g47_9]
    have g48_10 : reg n48 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb48, runBlock_reg _ _ _ a0 s47.zero (by decide), g47_10]
    have g48_11 : reg n48 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb48, runBlock_reg _ _ _ a1 s47.zero (by decide), g47_11]
    have g48_18 : reg n48 (18 : Fin 32) = out := by
      rw [rb48, runBlock_reg _ _ _ (18 : Fin 32) s47.zero (by decide), g47_18]
    have g48_19 : reg n48 (19 : Fin 32) = bp := by
      rw [rb48, runBlock_reg _ _ _ (19 : Fin 32) s47.zero (by decide), g47_19]
    have g48_20 : reg n48 (20 : Fin 32) = x20 := by
      rw [rb48, runBlock_reg _ _ _ (20 : Fin 32) s47.zero (by decide), g47_20]
    have g48_21 : reg n48 (21 : Fin 32) = x21 := by
      rw [rb48, runBlock_reg _ _ _ (21 : Fin 32) s47.zero (by decide), g47_21]
    have g48_22 : reg n48 (22 : Fin 32) = x22 := by
      rw [rb48, runBlock_reg _ _ _ (22 : Fin 32) s47.zero (by decide), g47_22]
    have g48_23 : reg n48 (23 : Fin 32) = x23 := by
      rw [rb48, runBlock_reg _ _ _ (23 : Fin 32) s47.zero (by decide), g47_23]
    have g48_24 : reg n48 (24 : Fin 32) = x24 := by
      rw [rb48, runBlock_reg _ _ _ (24 : Fin 32) s47.zero (by decide), g47_24]
    have g48_25 : reg n48 (25 : Fin 32) = x25 := by
      rw [rb48, runBlock_reg _ _ _ (25 : Fin 32) s47.zero (by decide), g47_25]
    have g48_26 : reg n48 (26 : Fin 32) = x26 := by
      rw [rb48, runBlock_reg _ _ _ (26 : Fin 32) s47.zero (by decide), g47_26]
    have g48_27 : reg n48 (27 : Fin 32) = x27 := by
      rw [rb48, runBlock_reg _ _ _ (27 : Fin 32) s47.zero (by decide), g47_27]
    have g48_8 : reg n48 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb48]; simp +decide only [runBlock, BInstr.run, svTr212b8, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g47_2, g47_3, g47_4, g47_8, g47_9, g47_10, g47_11, g47_18, g47_19, g47_20, g47_21, g47_22, g47_23, g47_24, g47_25, g47_26, g47_27, s47.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m48]; exact keep_kk47
    clear keep_kk47
    have w48_2e8 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m48]; exact w47_2e8
    have w48_2ec : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m48]; exact w47_2ec
    have w48_300 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m48]; exact w47_300
    have w48_304 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m48]; exact w47_304
    have w48_308 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m48]; exact w47_308
    have w48_30c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m48]; exact w47_30c
    have w48_310 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m48]; exact w47_310
    have w48_314 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m48]; exact w47_314
    have w48_318 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m48]; exact w47_318
    have w48_31c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m48]; exact w47_31c
    have w48_320 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m48]; exact w47_320
    have w48_324 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m48]; exact w47_324
    have w48_420 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m48]; exact w47_420
    have w48_424 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m48]; exact w47_424
    have w48_428 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m48]; exact w47_428
    have w48_42c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m48]; exact w47_42c
    have b48_424 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m48]; exact b47_424
    have b48_425 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m48]; exact b47_425
    have b48_426 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m48]; exact b47_426
    have b48_427 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m48]; exact b47_427
    clear b47_427 b47_426 b47_425 b47_424 w47_42c w47_428 w47_424 w47_420 w47_324 w47_320 w47_31c w47_318 w47_314 w47_310 w47_30c w47_308 w47_304 w47_300 w47_2ec w47_2e8 g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_11 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
    -- 0x12BA: j
    obtain ⟨n49, d49, u49⟩ := s48.jump E48.self sv_at_12ba (off' := 0x7A4) (by decide)
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
    have g49_8 : reg n49 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u49.regs, g48_8]
    have g49_9 : reg n49 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u49.regs, g48_9]
    have g49_10 : reg n49 a0 = BitVec.ofNat 32 0x0 := by rw [u49.regs, g48_10]
    have g49_11 : reg n49 a1 = BitVec.ofNat 32 0x0 := by rw [u49.regs, g48_11]
    have g49_18 : reg n49 (18 : Fin 32) = out := by rw [u49.regs, g48_18]
    have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [u49.regs, g48_19]
    have g49_20 : reg n49 (20 : Fin 32) = x20 := by rw [u49.regs, g48_20]
    have g49_21 : reg n49 (21 : Fin 32) = x21 := by rw [u49.regs, g48_21]
    have g49_22 : reg n49 (22 : Fin 32) = x22 := by rw [u49.regs, g48_22]
    have g49_23 : reg n49 (23 : Fin 32) = x23 := by rw [u49.regs, g48_23]
    have g49_24 : reg n49 (24 : Fin 32) = x24 := by rw [u49.regs, g48_24]
    have g49_25 : reg n49 (25 : Fin 32) = x25 := by rw [u49.regs, g48_25]
    have g49_26 : reg n49 (26 : Fin 32) = x26 := by rw [u49.regs, g48_26]
    have g49_27 : reg n49 (27 : Fin 32) = x27 := by rw [u49.regs, g48_27]
    have keep_kk49 : SvKeepL B n0.mem n49.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m49]; exact keep_kk48
    clear keep_kk48
    have w49_2e8 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m49]; exact w48_2e8
    have w49_2ec : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m49]; exact w48_2ec
    have w49_300 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m49]; exact w48_300
    have w49_304 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m49]; exact w48_304
    have w49_308 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m49]; exact w48_308
    have w49_30c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m49]; exact w48_30c
    have w49_310 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m49]; exact w48_310
    have w49_314 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m49]; exact w48_314
    have w49_318 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m49]; exact w48_318
    have w49_31c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m49]; exact w48_31c
    have w49_320 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m49]; exact w48_320
    have w49_324 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m49]; exact w48_324
    have w49_420 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m49]; exact w48_420
    have w49_424 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m49]; exact w48_424
    have w49_428 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m49]; exact w48_428
    have w49_42c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m49]; exact w48_42c
    have b49_424 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m49]; exact b48_424
    have b49_425 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m49]; exact b48_425
    have b49_426 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m49]; exact b48_426
    have b49_427 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m49]; exact b48_427
    clear b48_427 b48_426 b48_425 b48_424 w48_42c w48_428 w48_424 w48_420 w48_324 w48_320 w48_31c w48_318 w48_314 w48_310 w48_30c w48_308 w48_304 w48_300 w48_2ec w48_2e8 g48_8 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_11 g48_10 g48_9 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 rb48 s48 m48 u48 c48
    exact .inl ⟨(fun ⟨tl2', h0', h1', op13', ol13', h2', to13', h3', h4', tl21', h5', h6', tl32', h7', h8', h9', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [ht13] at h3'; cases h3'; rw [hr21] at h5'; cases h5'; rw [hr32] at h7'; cases h7'; rw [hr43] at h9'; cases h9'), sv_fail F E49 s49 t49 (fun x hx => (fR49 x hx).trans (fM x hx).symm) V49 hret g49_2 g49_18 hO g49_3 g49_4 (by rw [g49_8]; sv_code)⟩
  obtain ⟨te43, hte43⟩ := ii_ok_elem hr43
  obtain ⟨d8_43, d12_43⟩ := A43 te43 hte43
  rw [hr43] at R43
  obtain ⟨a0_43, a1_43⟩ := R43
  have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x0 := a0_43
  have g43_11 : reg n43 a1 = BitVec.ofNat 32 0x1 := by rw [a1_43]; rfl
  have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := keep_kk42.trans K43
  clear keep_kk42
  have w43_2e8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K43.w32 (by decide) (by decide)).trans w42_2e8
  have w43_2ec : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K43.w32 (by decide) (by decide)).trans w42_2ec
  have w43_300 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := (K43.w32 (by decide) (by decide)).trans w42_300
  have w43_304 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := (K43.w32 (by decide) (by decide)).trans w42_304
  have w43_308 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := (K43.w32 (by decide) (by decide)).trans w42_308
  have w43_30c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := (K43.w32 (by decide) (by decide)).trans w42_30c
  have w43_310 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := (K43.w32 (by decide) (by decide)).trans w42_310
  have w43_314 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := (K43.w32 (by decide) (by decide)).trans w42_314
  have w43_318 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := (K43.w32 (by decide) (by decide)).trans w42_318
  have w43_31c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := (K43.w32 (by decide) (by decide)).trans w42_31c
  have w43_320 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K43.w32 (by decide) (by decide)).trans w42_320
  have w43_324 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := (K43.w32 (by decide) (by decide)).trans w42_324
  have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K43.w32 (by decide) (by decide)).trans w42_420
  have w43_424 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := (K43.w32 (by decide) (by decide)).trans w42_424
  have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := (K43.w32 (by decide) (by decide)).trans w42_428
  have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := (K43.w32 (by decide) (by decide)).trans w42_42c
  have b43_424 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := (K43.b8 (by decide) (by decide)).trans b42_424
  have b43_425 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := (K43.b8 (by decide) (by decide)).trans b42_425
  have b43_426 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := (K43.b8 (by decide) (by decide)).trans b42_426
  have b43_427 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := (K43.b8 (by decide) (by decide)).trans b42_427
  have w43_328 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) + BitVec.ofNat 32 (te43.header + te43.len) := d8_43
  have w43_32c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (BitVec.ofNat 32 tl32.len) - BitVec.ofNat 32 (te43.header + te43.len) := d12_43
  clear b42_427 b42_426 b42_425 b42_424 w42_42c w42_428 w42_424 w42_420 w42_32c w42_328 w42_324 w42_320 w42_31c w42_318 w42_314 w42_310 w42_30c w42_308 w42_304 w42_300 w42_2ec w42_2e8 g42_11 g42_10 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
  -- 0xBFA
  obtain ⟨n44, c44, u44⟩ := s43.block svTr2bfa E43.self svTr2bfa_end
    ⟨trivial, trivial, trivial⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have s44 : St n44.mem SV n44 0xBFE (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have rb44 : ∀ q, reg n44 q = (runBlock svTr2bfa (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
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
  have g44_9 : reg n44 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by
    rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
  have g44_11 : reg n44 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb44, runBlock_reg _ _ _ a1 s43.zero (by decide), g43_11]
  have g44_18 : reg n44 (18 : Fin 32) = out := by
    rw [rb44, runBlock_reg _ _ _ (18 : Fin 32) s43.zero (by decide), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = bp := by
    rw [rb44, runBlock_reg _ _ _ (19 : Fin 32) s43.zero (by decide), g43_19]
  have g44_20 : reg n44 (20 : Fin 32) = x20 := by
    rw [rb44, runBlock_reg _ _ _ (20 : Fin 32) s43.zero (by decide), g43_20]
  have g44_21 : reg n44 (21 : Fin 32) = x21 := by
    rw [rb44, runBlock_reg _ _ _ (21 : Fin 32) s43.zero (by decide), g43_21]
  have g44_22 : reg n44 (22 : Fin 32) = x22 := by
    rw [rb44, runBlock_reg _ _ _ (22 : Fin 32) s43.zero (by decide), g43_22]
  have g44_23 : reg n44 (23 : Fin 32) = x23 := by
    rw [rb44, runBlock_reg _ _ _ (23 : Fin 32) s43.zero (by decide), g43_23]
  have g44_24 : reg n44 (24 : Fin 32) = x24 := by
    rw [rb44, runBlock_reg _ _ _ (24 : Fin 32) s43.zero (by decide), g43_24]
  have g44_25 : reg n44 (25 : Fin 32) = x25 := by
    rw [rb44, runBlock_reg _ _ _ (25 : Fin 32) s43.zero (by decide), g43_25]
  have g44_26 : reg n44 (26 : Fin 32) = x26 := by
    rw [rb44, runBlock_reg _ _ _ (26 : Fin 32) s43.zero (by decide), g43_26]
  have g44_27 : reg n44 (27 : Fin 32) = x27 := by
    rw [rb44, runBlock_reg _ _ _ (27 : Fin 32) s43.zero (by decide), g43_27]
  have g44_8 : reg n44 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svTr2bfa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svTr2bfa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m44]; exact keep_kk43
  clear keep_kk43
  have w44_2e8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m44]; exact w43_2e8
  have w44_2ec : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m44]; exact w43_2ec
  have w44_300 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m44]; exact w43_300
  have w44_304 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m44]; exact w43_304
  have w44_308 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m44]; exact w43_308
  have w44_30c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m44]; exact w43_30c
  have w44_310 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m44]; exact w43_310
  have w44_314 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m44]; exact w43_314
  have w44_318 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m44]; exact w43_318
  have w44_31c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m44]; exact w43_31c
  have w44_320 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m44]; exact w43_320
  have w44_324 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m44]; exact w43_324
  have w44_328 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m44]; exact w43_328
  have w44_32c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (BitVec.ofNat 32 tl32.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m44]; exact w43_32c
  have w44_420 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m44]; exact w43_420
  have w44_424 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m44]; exact w43_424
  have w44_428 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m44]; exact w43_428
  have w44_42c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m44]; exact w43_42c
  have b44_424 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m44]; exact b43_424
  have b44_425 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m44]; exact b43_425
  have b44_426 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m44]; exact b43_426
  have b44_427 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m44]; exact b43_427
  clear w43_32c w43_328 b43_427 b43_426 b43_425 b43_424 w43_42c w43_428 w43_424 w43_420 w43_324 w43_320 w43_31c w43_318 w43_314 w43_310 w43_30c w43_308 w43_304 w43_300 w43_2ec w43_2e8 g43_11 g43_10 a1_43 a0_43 d12_43 d8_43 g43_2 g43_27 g43_26 g43_25 g43_24 g43_23 g43_22 g43_21 g43_20 g43_19 g43_18 g43_9 g43_8 g43_4 g43_3 V43 E43 fR43 t43 fr43 A43 K43 rk43 sp43 s43 c43
  -- 0xBFE: branch, not taken
  obtain ⟨n45, d45, u45⟩ := s44.notTaken E44.self 0xC02 sv_at_bfe
    (by decide) (by rw [g44_10, s44.zero]; decide)
  have s45 : St n45.mem SV n45 0xC02 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
  have m45 : n45.mem = n44.mem := u45.mem
  have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
  have t45 : Steps n0 n45 := t44.trans (.single d45)
  have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.same m45
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, g44_4]
  have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_8]
  have g45_9 : reg n45 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u45.regs, g44_9]
  have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x0 := by rw [u45.regs, g44_10]
  have g45_11 : reg n45 a1 = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_11]
  have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
  have g45_20 : reg n45 (20 : Fin 32) = x20 := by rw [u45.regs, g44_20]
  have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [u45.regs, g44_21]
  have g45_22 : reg n45 (22 : Fin 32) = x22 := by rw [u45.regs, g44_22]
  have g45_23 : reg n45 (23 : Fin 32) = x23 := by rw [u45.regs, g44_23]
  have g45_24 : reg n45 (24 : Fin 32) = x24 := by rw [u45.regs, g44_24]
  have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [u45.regs, g44_25]
  have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [u45.regs, g44_26]
  have g45_27 : reg n45 (27 : Fin 32) = x27 := by rw [u45.regs, g44_27]
  have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m45]; exact keep_kk44
  clear keep_kk44
  have w45_2e8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m45]; exact w44_2e8
  have w45_2ec : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m45]; exact w44_2ec
  have w45_300 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m45]; exact w44_300
  have w45_304 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m45]; exact w44_304
  have w45_308 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m45]; exact w44_308
  have w45_30c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m45]; exact w44_30c
  have w45_310 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m45]; exact w44_310
  have w45_314 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m45]; exact w44_314
  have w45_318 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m45]; exact w44_318
  have w45_31c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m45]; exact w44_31c
  have w45_320 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m45]; exact w44_320
  have w45_324 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m45]; exact w44_324
  have w45_328 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m45]; exact w44_328
  have w45_32c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (BitVec.ofNat 32 tl32.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m45]; exact w44_32c
  have w45_420 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m45]; exact w44_420
  have w45_424 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m45]; exact w44_424
  have w45_428 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m45]; exact w44_428
  have w45_42c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m45]; exact w44_42c
  have b45_424 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m45]; exact b44_424
  have b45_425 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m45]; exact b44_425
  have b45_426 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m45]; exact b44_426
  have b45_427 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m45]; exact b44_427
  clear b44_427 b44_426 b44_425 b44_424 w44_42c w44_428 w44_424 w44_420 w44_32c w44_328 w44_324 w44_320 w44_31c w44_318 w44_314 w44_310 w44_30c w44_308 w44_304 w44_300 w44_2ec w44_2e8 g44_10 g44_8 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_11 g44_9 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
  -- 0xC02
  obtain ⟨n46, c46, u46⟩ := s45.block svTr2c02 E45.self svTr2c02_end
    ⟨trivial, trivial⟩
  have m46 : n46.mem = n45.mem := u46.mem
  have s46 : St n46.mem SV n46 0xC04 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
  have rb46 : ∀ q, reg n46 q = (runBlock svTr2c02 (n45.mem, reg n45)).2 q := fun q => by rw [u46.regs]
  have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
  have t46 : Steps n0 n46 := t45.trans c46
  have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.same m46
  have g46_2 : reg n46 sp = B + 0x21A0 := by
    rw [rb46, runBlock_reg _ _ _ sp s45.zero (by decide), g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb46, runBlock_reg _ _ _ (3 : Fin 32) s45.zero (by decide), g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb46, runBlock_reg _ _ _ (4 : Fin 32) s45.zero (by decide), g45_4]
  have g46_9 : reg n46 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by
    rw [rb46, runBlock_reg _ _ _ (9 : Fin 32) s45.zero (by decide), g45_9]
  have g46_10 : reg n46 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb46, runBlock_reg _ _ _ a0 s45.zero (by decide), g45_10]
  have g46_11 : reg n46 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb46, runBlock_reg _ _ _ a1 s45.zero (by decide), g45_11]
  have g46_18 : reg n46 (18 : Fin 32) = out := by
    rw [rb46, runBlock_reg _ _ _ (18 : Fin 32) s45.zero (by decide), g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by
    rw [rb46, runBlock_reg _ _ _ (19 : Fin 32) s45.zero (by decide), g45_19]
  have g46_20 : reg n46 (20 : Fin 32) = x20 := by
    rw [rb46, runBlock_reg _ _ _ (20 : Fin 32) s45.zero (by decide), g45_20]
  have g46_21 : reg n46 (21 : Fin 32) = x21 := by
    rw [rb46, runBlock_reg _ _ _ (21 : Fin 32) s45.zero (by decide), g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = x22 := by
    rw [rb46, runBlock_reg _ _ _ (22 : Fin 32) s45.zero (by decide), g45_22]
  have g46_23 : reg n46 (23 : Fin 32) = x23 := by
    rw [rb46, runBlock_reg _ _ _ (23 : Fin 32) s45.zero (by decide), g45_23]
  have g46_24 : reg n46 (24 : Fin 32) = x24 := by
    rw [rb46, runBlock_reg _ _ _ (24 : Fin 32) s45.zero (by decide), g45_24]
  have g46_25 : reg n46 (25 : Fin 32) = x25 := by
    rw [rb46, runBlock_reg _ _ _ (25 : Fin 32) s45.zero (by decide), g45_25]
  have g46_26 : reg n46 (26 : Fin 32) = x26 := by
    rw [rb46, runBlock_reg _ _ _ (26 : Fin 32) s45.zero (by decide), g45_26]
  have g46_27 : reg n46 (27 : Fin 32) = x27 := by
    rw [rb46, runBlock_reg _ _ _ (27 : Fin 32) s45.zero (by decide), g45_27]
  have g46_8 : reg n46 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb46]; simp +decide only [runBlock, BInstr.run, svTr2c02, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g45_2, g45_3, g45_4, g45_8, g45_9, g45_10, g45_11, g45_18, g45_19, g45_20, g45_21, g45_22, g45_23, g45_24, g45_25, g45_26, g45_27, s45.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m46]; exact keep_kk45
  clear keep_kk45
  have w46_2e8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m46]; exact w45_2e8
  have w46_2ec : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m46]; exact w45_2ec
  have w46_300 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m46]; exact w45_300
  have w46_304 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m46]; exact w45_304
  have w46_308 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m46]; exact w45_308
  have w46_30c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m46]; exact w45_30c
  have w46_310 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m46]; exact w45_310
  have w46_314 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m46]; exact w45_314
  have w46_318 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m46]; exact w45_318
  have w46_31c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m46]; exact w45_31c
  have w46_320 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m46]; exact w45_320
  have w46_324 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m46]; exact w45_324
  have w46_328 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m46]; exact w45_328
  have w46_32c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (BitVec.ofNat 32 tl32.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m46]; exact w45_32c
  have w46_420 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m46]; exact w45_420
  have w46_424 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m46]; exact w45_424
  have w46_428 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m46]; exact w45_428
  have w46_42c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m46]; exact w45_42c
  have b46_424 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m46]; exact b45_424
  have b46_425 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m46]; exact b45_425
  have b46_426 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m46]; exact b45_426
  have b46_427 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m46]; exact b45_427
  clear b45_427 b45_426 b45_425 b45_424 w45_42c w45_428 w45_424 w45_420 w45_32c w45_328 w45_324 w45_320 w45_31c w45_318 w45_314 w45_310 w45_30c w45_308 w45_304 w45_300 w45_2ec w45_2e8 g45_27 g45_26 g45_25 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_11 g45_10 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45
  -- 0xC04: branch, not taken
  obtain ⟨n47, d47, u47⟩ := s46.notTaken E46.self 0xC08 sv_at_c04
    (by decide) (by rw [g46_8, s46.zero]; decide)
  have s47 : St n47.mem SV n47 0xC08 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
  have m47 : n47.mem = n46.mem := u47.mem
  have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
  have t47 : Steps n0 n47 := t46.trans (.single d47)
  have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : SvCode n47.mem := E46.fr F fr47
  have V47 : SvSaves B n47.mem v := V46.same m47
  have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
  have g47_8 : reg n47 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u47.regs, g46_8]
  have g47_9 : reg n47 (9 : Fin 32) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [u47.regs, g46_9]
  have g47_10 : reg n47 a0 = BitVec.ofNat 32 0x0 := by rw [u47.regs, g46_10]
  have g47_11 : reg n47 a1 = BitVec.ofNat 32 0x1 := by rw [u47.regs, g46_11]
  have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
  have g47_20 : reg n47 (20 : Fin 32) = x20 := by rw [u47.regs, g46_20]
  have g47_21 : reg n47 (21 : Fin 32) = x21 := by rw [u47.regs, g46_21]
  have g47_22 : reg n47 (22 : Fin 32) = x22 := by rw [u47.regs, g46_22]
  have g47_23 : reg n47 (23 : Fin 32) = x23 := by rw [u47.regs, g46_23]
  have g47_24 : reg n47 (24 : Fin 32) = x24 := by rw [u47.regs, g46_24]
  have g47_25 : reg n47 (25 : Fin 32) = x25 := by rw [u47.regs, g46_25]
  have g47_26 : reg n47 (26 : Fin 32) = x26 := by rw [u47.regs, g46_26]
  have g47_27 : reg n47 (27 : Fin 32) = x27 := by rw [u47.regs, g46_27]
  have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x420, 0x10), (0x2E8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x420, 0x10), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x420, 0x10), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8)] := by rw [m47]; exact keep_kk46
  clear keep_kk46
  have w47_2e8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m47]; exact w46_2e8
  have w47_2ec : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m47]; exact w46_2ec
  have w47_300 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x300) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m47]; exact w46_300
  have w47_304 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x304) = BitVec.ofNat 32 tl2.len := by rw [m47]; exact w46_304
  have w47_308 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x308) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m47]; exact w46_308
  have w47_30c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x30C) = ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (to13.header + to13.len)) - BitVec.ofNat 32 (tl21.header + tl21.len) := by rw [m47]; exact w46_30c
  have w47_310 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x310) = (((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header := by rw [m47]; exact w46_310
  have w47_314 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x314) = BitVec.ofNat 32 tl21.len := by rw [m47]; exact w46_314
  have w47_318 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x318) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m47]; exact w46_318
  have w47_31c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x31C) = (BitVec.ofNat 32 tl21.len) - BitVec.ofNat 32 (tl32.header + tl32.len) := by rw [m47]; exact w46_31c
  have w47_320 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m47]; exact w46_320
  have w47_324 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl32.len := by rw [m47]; exact w46_324
  have w47_328 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m47]; exact w46_328
  have w47_32c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (BitVec.ofNat 32 tl32.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m47]; exact w46_32c
  have w47_420 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m47]; exact w46_420
  have w47_424 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl32.len := by rw [m47]; exact w46_424
  have w47_428 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (to13.header + to13.len)) + BitVec.ofNat 32 tl21.header) + BitVec.ofNat 32 tl32.header := by rw [m47]; exact w46_428
  have w47_42c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl32.len := by rw [m47]; exact w46_42c
  have b47_424 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl32.len).extractLsb' 0 8 := by rw [m47]; exact b46_424
  have b47_425 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl32.len).extractLsb' 8 8 := by rw [m47]; exact b46_425
  have b47_426 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl32.len).extractLsb' 16 8 := by rw [m47]; exact b46_426
  have b47_427 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl32.len).extractLsb' 24 8 := by rw [m47]; exact b46_427
  clear b46_427 b46_426 b46_425 b46_424 w46_42c w46_428 w46_424 w46_420 w46_32c w46_328 w46_324 w46_320 w46_31c w46_318 w46_314 w46_310 w46_30c w46_308 w46_304 w46_300 w46_2ec w46_2e8 g46_8 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_11 g46_10 g46_9 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 rb46 s46 m46 u46 c46
  exact .inr ⟨tl2, hr2, hrem, op13, ol13, hr13, to13, ht13, hsd, tl21, hr21, hcrem, tl32, hr32, herem, hr43, te43, hte43, n47, t47, s47, E47, V47, fR47, g47_2, g47_3, g47_4, g47_18, g47_19, g47_20, g47_21, g47_22, g47_23, g47_24, g47_25, g47_26, g47_27, w47_328, w47_32c, keep_kk47.mono (by decide)⟩

end C3.RV32.Sv
